use std::error::Error;
use std::fs::File;
use std::io::Read;
use bstr::ByteSlice;
use regex::bytes::Regex;
use z3::{Config, Context, SatResult, Solver};
use z3::ast::{Ast, Bool, Int};

fn parse(bytes: &[u8]) -> i32 {
    let mut val = 0;
    for b in bytes {
        val = 10 * val + (*b - b'0');
    }
    val as i32
}

fn parse_blacks(group_regex: &Regex, cell_regex: &Regex, buf: &[u8]) -> Vec<Vec<i32>> {
    let mut blacks = Vec::new();
    for group_cap in group_regex.captures_iter(&buf) {
        let mut group = Vec::new();
        for cell_cap in cell_regex.captures_iter(&group_cap[1]) {
            let val = parse(&cell_cap[1]);
            if val > 0 {
                group.push(val);
            }
        }
        blacks.push(group);
    }
    blacks
}

fn add_gap_constraints<'ctx>(prefix: &str, blacks: &Vec<Vec<i32>>, gap_total: usize, cell_vars: &[Bool<'ctx>], cell_index: impl Fn(usize, usize) -> usize, solver: &Solver<'ctx>) {
    let ctx = solver.get_context();
    for (i, blacks) in blacks.iter().enumerate() {
        let mut gaps = Vec::new();
        let mut constraints = vec![Vec::new(); gap_total];
        let mut sum = 0;
        for (j, black) in blacks.iter().enumerate() {
            let gap = Int::new_const(ctx, format!("{}_gap_{}_{}", prefix, i, j));
            if j == 0 {
                solver.assert(&gap.ge(&Int::from_i64(ctx, 0)));
            } else {
                solver.assert(&gap.ge(&Int::from_i64(ctx, 1)));
            }
            gaps.push(gap);

            for (k, constraint) in constraints.iter_mut().enumerate() {
                // gap_sum <= k - black_sum && k - black_sum - black < gap_sum
                constraint.push(Bool::and(ctx, &[
                    &Int::add(ctx, &gaps.iter().collect::<Vec<_>>()).le(&Int::from_i64(ctx, k as i64 - sum as i64)),
                    &Int::add(ctx, &gaps.iter().collect::<Vec<_>>()).gt(&Int::from_i64(ctx, k as i64 - sum as i64 - *black as i64))
                ]));
            }
            sum += *black;
        }
        let gap = Int::new_const(ctx, format!("{}_gap_{}_{}", prefix, i, blacks.len()));
        solver.assert(&gap.ge(&Int::from_i64(ctx, 0)));
        gaps.push(gap);
        solver.assert(&Int::add(ctx, &gaps.iter().collect::<Vec<_>>())._eq(&Int::from_i64(ctx, gap_total as i64 - sum as i64)));

        for (j, constraint) in constraints.iter().enumerate() {
            let cell = &cell_vars[cell_index(i, j)];
            solver.assert(&cell._eq(&Bool::or(ctx, &constraint.iter().collect::<Vec<_>>())));
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut file = File::open("/Users/twilson/code/nonograms/nonograms.html")?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf)?;

    let group_regex = Regex::new(r#"<div class="task-group(.*?</div>)</div>"#)?;
    let cell_regex = Regex::new(r#"<div class="task-cell.*?>(.*?)</div>"#)?;

    let v_index = buf.find(r#"<div id="taskTop""#).unwrap();
    let h_index = v_index + buf[v_index..].find(r#"<div id="taskLeft""#).unwrap();

    let v_blacks = parse_blacks(&group_regex, &cell_regex, &buf[v_index..h_index]);
    let h_blacks = parse_blacks(&group_regex, &cell_regex, &buf[h_index..]);

    let height = h_blacks.len();
    let width = v_blacks.len();

    let ctx = &Context::new(&Config::new());
    let solver = Solver::new(ctx);
    let mut cell_vars = Vec::new();
    for i in 0..height {
        for j in 0..width {
            cell_vars.push(Bool::new_const(ctx, format!("cell_{}_{}", i, j)));
        }
    }
    add_gap_constraints("v", &v_blacks, height, &cell_vars, |i, j| width * j + i, &solver);
    add_gap_constraints("h", &h_blacks, width, &cell_vars, |i, j| width * i + j, &solver);
    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();

    for i in 0..height {
        if i != 0 && i % 5 == 0 {
            println!();
        }
        for j in 0..width {
            let cell = model.eval(&cell_vars[width * i + j], false).unwrap().as_bool().unwrap();
            if j != 0 && j % 5 == 0 {
                print!("  ");
            }
            if cell {
                print!("⬛");
            } else {
                print!("⬜");
            }
        }
        println!();
    }
    Ok(())
}
