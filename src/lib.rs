#![feature(type_ascription)]
#![cfg_attr(not(feature = "contracts"), feature(stmt_expr_attributes, proc_macro_hygiene))]
extern crate creusot_contracts;

use creusot_contracts::*;

#[ensures(forall<i : Int> 0 <= i && i < (@^v).len() ==> (@^v)[i] == 0u32)]
#[ensures((@*v).len() == (@^v).len())]
pub fn all_zero(v: &mut Vec<u32>) {
    let mut i = 0;
    let old_v = ghost! { v };
    // This invariant is because why3 can't determine that the prophecy isn't modified by the loop
    // Either Why3 or Creusot should be improved to do this automaticallly (probably why3)
    #[invariant(proph_const, ^v == ^old_v.inner())]
    #[invariant(in_bounds, (@*v).len() == (@*old_v.inner()).len())]
    #[invariant(all_zero, forall<j : Int> 0 <= j && j < i.into() ==> (@*v)[j] == 0u32)]
    while i < v.len() {
        v[i] = 0;
        i += 1;
    }
}