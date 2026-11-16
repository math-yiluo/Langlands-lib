# Étale descent of affine groups over an affine base

This internal construction works in an arbitrary universe. Let `p : S → B`
be a surjective étale morphism, let `B` be affine, let `G` be an actual group
scheme over `S` whose structure morphism is affine, and let
`D : Descent.Datum p G` be a Čech descent datum.

`Datum.etaleAffineBaseSolution` constructs a `Solution D`. The instance
`Datum.etaleAffineBaseSolution_isAffine` proves that the descended group's
underlying scheme is affine. The covering scheme `S` need not be affine,
and `p` need not be quasi-compact. There are no field, smoothness, finite
type, connectedness, or commutativity hypotheses.

The affine base is compact. `affineEtaleRefinement p` therefore gives an
affine scheme `V` and an étale map `q : V → S` such that `q ≫ p` is
surjective. Pullback of the affine structure morphism of `G` to the affine
scheme `V` has affine total space. The existing affine group descent
construction `Datum.affineSolution` solves `D.refine q`.
`Datum.solutionOfRefinement` then recovers a solution of the original
datum, keeping the same descended group. Its affineness consequently
follows from `Datum.affineSolution_isAffine`.

The provenance is internal: this module composes the actual finite affine
refinement, affine group descent, and recovery constructions in its
imports. Its input contains no solution or effectivity premise. Arbitrary
base schemes still require a separate gluing argument.
