#![cfg_attr(not(feature = "contracts"), feature(stmt_expr_attributes, proc_macro_hygiene))]
extern crate creusot_contracts;
use creusot_contracts::*;

#[allow(non_camel_case_types)] type uz = usize;

#[cfg(not(feature = "contracts"))]
pub trait Model {}

#[logic] fn lmax(a:Int, b:Int)-> Int {pearlite! {if a<b {b} else {a}}}

#[ensures(@result == lmax(@a,@b))]
fn maxz(a:uz, b:uz)-> uz {if a<b {b} else {a}}
#[ensures(@result == lmax(@a-@b,0))]
fn sub(a:uz, b:uz)-> uz {if a<b {0} else {a-b}}

#[ensures( (@result).len()==lmax(@l,(@s).len()) )]
#[ensures(forall<i:uz> @i < lmax(@l-(@s).len(), 0) ==> @(@result)[@i] == @c)]
#[ensures
  ( forall<i:uz> @i >= lmax(@l-(@s).len(), 0) && @i < lmax(@l,(@s).len())
    ==> @(@result)[@i] == @(@s)[@i - lmax(@l-(@s).len(), 0)]              )]
pub fn leftpad<C:Copy+Model>(c:C, l:uz, s:&[C])-> Vec<C>
  { let rl = maxz(l,s.len());  let pl = sub(l,s.len());
    let (mut r, mut i) = (Vec::<C>::with_capacity(rl), 0usize);

    #[invariant(a1, @i>=0 && @i<=@pl && (@r).len()==@i)]
    #[invariant(a2, forall<j:uz> @j<@i ==> @(@r)[@j] == @c)]
    while i<pl {r.push(c); i+=1}

    #[invariant(b1, @i>=@pl && @i<=@rl && (@r).len()==@i)]
    #[invariant(b2, forall<j:uz> @j>=@pl && @j<@i ==> @(@r)[@j] == @(@s)[@j-@pl])]
    #[invariant(b3, forall<j:uz> @j<@pl ==> @(@r)[@j] == @c)]
    while i<rl {r.push(s[i-pl]); i+=1}
    r                                                                              }
