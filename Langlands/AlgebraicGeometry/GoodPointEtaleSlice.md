# A chosen etale slice through a good point

`GoodPointEtaleSliceData t s x` packages a scheme `Z`, a morphism
`g : Z → U`, and a point `a : Z` mapping to `x`, together with proofs
that `g` is a preimmersion locally of finite presentation and that
`Z ×_U R → R → U`, using the `t` pullback and then `s`, is etale.
No surjectivity condition is part of this data.

For an equivalence relation `t,s : R → U` with `s` smooth and a common
identity section `e`, `goodPointEtaleSlice` chooses such data at every
supplied good point `x`. Its input is precisely the maximal ideal
equality `SmoothRelationGoodPoint.IsGoodPoint t s e x`. Its construction
uses classical choice on the fully proved
`exists_etale_slice_of_isGoodPoint`, whose implemented differential
slicing and propagation argument is described in
`GoodPointEtaleSliceProof.md`. The chosen data are not canonical.

This is an internal local construction by Workers 101, 303 and 424.
The candidate includes their algebraic differential slicing,
good-point chart comparison, and relation propagation proofs, together
with the unchanged supporting definitions and statements they import.
No unproved Library proposition is assumed. This construction supplies
one local input to the smooth equivalence relation slicing theorem.
Existence of a good point on every orbit and a globally surjective
family of slices remain separate obligations. Acceptance of this
definition candidate does not certify the final exact theorem.
