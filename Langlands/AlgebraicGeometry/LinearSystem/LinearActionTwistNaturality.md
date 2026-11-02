# Base change of the relative projective linear-action twist comparison

For arbitrary commutative rings `K` and `R`, a scheme morphism `f : T ⟶ S`,
structure maps `a : S ⟶ Spec K` and `b : T ⟶ Spec R`, and a ring homomorphism
`φ : K →+* R` satisfying `b ≫ Spec.map φ = f ≫ a`, this module proves base-change
compatibility of the actual relative degree-one twist comparison. All rings and
schemes share the arbitrary universe of the existing projective-space API, and
the projective dimension `n` is any natural number.

Write `g = RelativeProjectiveSpace.map n f`, `M = (twistOne S n).obj`,
`N = (twistOne T n).obj`, and let `δ : g^*M ≅ N` be the underlying module-sheaf
isomorphism of the existing `twistOnePullbackIso n f`. For an invertible
`K`-linear coordinate map `e`, `relativeLinearActionTwistBaseChangeIso a f e`
constructs the actual isomorphism

`g^*((linearAction a e)^*M) ≅ N`

by pulling back the previously constructed action comparison and composing with
`δ`. Its definition requires only `a`, `f`, and `e`.

Given an invertible `R`-linear map `e'` whose matrix coefficients are the images
under `φ` of those of `e`, the existing scheme-map naturality supplies the square
`g ≫ linearAction a e = linearAction b e' ≫ g`.
`relativeLinearActionTwistBaseChangeIso_naturality` identifies the constructed
isomorphism with the other path: first the canonical `squarePullbackIso`, then
the pullback of `δ` along `linearAction b e'`, and finally the action comparison
for `b` and `e'`. Thus the theorem asserts equality of the specified actual
isomorphisms, including the canonical pullback-composition and equality
transports. `twistOnePullbackIso_changed_coordinate` and
`relativeLinearActionTwistBaseChangeIso_coordinate` give the corresponding
formulas on changed and twice pulled-back homogeneous coordinates.

`globalLinearActionTwistBaseChangeIso` specializes the object to `a = S.toSpecΓ`.
Its naturality theorem uses `φ = f.appTop.hom` and the actual
`coordinatePullback n f e`. It consequently includes pullback of every global
matrix coefficient.

The proof is derived from the existing constructions. First,
`pullbackComp_inv_coordinate` and `squarePullbackIso_coordinate` evaluate the
canonical transports on actual sections. Two successive pullbacks of the
covering coordinate frames and module-sheaf extensionality prove the general
square criterion `pullback_comparison_square`. Naturality of global scalars,
using `scalarsFromBase_specMap` and composition of `appTop`, proves that a
coordinate-preserving comparison also transports linear combinations when all
coefficients are mapped by `φ`. The generic linear square criterion then applies
to the actual relative coordinate sections and the proved coordinate laws of
the action comparisons. This uses no additional source assertion or supplied
sheaf-comparison premise.

This supporting construction leaves tautological-bundle gluing, cubic embedding,
and the ordinary moduli representability conclusion to subsequent work.
