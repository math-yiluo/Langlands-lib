# Weight and root comparison under injective character pullback

This internal support module compares the actual adjoint weight spaces for a
homomorphism between split tori over any field. It uses the published
`weightSpace_comp_eq_iSup` and `mem_roots_comp_iff` from
`Torus.WeightRestriction`; its conclusions retain the explicit hypotheses
listed below.

For `t : T → T'` and `i' : T' → G'`, injectivity of actual integral character
pullback makes the fiber above `t ≫ χ` consist of `χ` alone. The supremum formula
therefore proves equality of the pulled-back weight space with the original
weight space. `Lie.weightSpaceCompEquiv` is the linear equivalence associated to
this equality; it fixes the underlying actual dual-number Lie vector.
The ambient target is affine and locally of finite type, and both tori are
split, as required by the published weight decomposition.

Given a square `i ≫ q = t ≫ i'` and equality of root supports for the action of
`T` through `i` and `i ≫ q`, `roots_bijOn_of_comp_eq` proves that character
pullback is a bijection from the actual roots of `i'` onto the roots of `i`.
Injectivity ensures that a nonzero target root remains nonzero on pullback;
the published restriction criterion supplies both the forward and the
surjectivity implications. Equality of root supports is an explicit input.

The final dimension adapter assumes that `t` is an actual torus isogeny,
that both torus inclusions are monomorphic, and that each all-test torus
centralizer equals the actual pointwise range of its inclusion.
`Lie.SplitTorusCoordinates` then equates the original zero-weight dimensions.
Flat surjectivity of the torus isogeny makes character pullback injective.
The weight-space equality at the zero character identifies the pulled-back
target zero weight with its original zero weight, yielding exactly the
comparison between `weightSpace i 0` and `weightSpace (i ≫ q) 0`.

These are consequences of the named constructions, with no external
literature assertion added. The module does not prove the self-centralizer
equalities, equality of total ambient Lie dimensions, or the full central
isogeny root-datum theorem. No separability or characteristic hypothesis is
used in the torus-isogeny adapter.
