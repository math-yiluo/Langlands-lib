# Proof of naturality of square-zero Picard obstructions under morphisms of thickenings

Contributors: Worker 23 (Task 5894), Worker 217 and Worker 221.

## Statement proved

`Langlands.AlgebraicGeometry.Picard.squareZeroObstructionMorphismNaturality` proves
`Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement.{u}`, which is
published in module `Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement`.

The setting is a ring `R` and a morphism `f : X' ⟶ X` of schemes over `Spec R`. Let
`i : Y ⟶ X` and `i' : Y' ⟶ X'` be closed immersions whose ideals square to zero, and let
`g : Y' ⟶ Y` satisfy `i' ≫ f = g ≫ i`. All four schemes are quasi-compact. Let
`k : I ⟶ f_* I'` be a map of ideal modules that is compatible with the inclusions into the
structure sheaves. Then for every Picard class `y` on `Y`, the obstruction of `g^* y` in
`H²(X', I')` equals the image of the obstruction of `y` in `H²(X, I)` under two maps: the
cohomology pullback `H²(X, I) ⟶ H²(X', f^* I)`, then the map induced by the adjoint
`f^* I ⟶ I'` of `k`. Both obstructions are compared in relative module cohomology
`relativeCohomology _ 2`, after transport by `relativeIdealCohomologyAddEquiv`, and the pullback
is `relativeCohomologyPullback f I 2`. The statement's Markdown gives the exact Lean dictionary.

## Proof

The proof is a single term that combines two Library results.

1. `Picard.SquareZeroMorphismRelativeComparison.squareZeroObstructionMorphismNaturality_of_relativeComparison`
   (module `Langlands.AlgebraicGeometry.Picard.SquareZeroMorphismRelativeComparison`) proves the
   target from
   `Modules.AbelianSheafComparison.RelativeAbelianSheafCohomologyPullbackStatement.{u}`. That
   statement says that the relative additive comparison `relativeHAddEquiv` between module
   cohomology and Mathlib sheaf cohomology of the underlying abelian sheaf commutes with
   pullback along an arbitrary morphism over `Spec R`, with a coefficient arrow `k : M ⟶ f_* N`
   and its adjoint.
2. `Modules.AbelianSheafComparison.relativeAbelianSheafCohomologyPullback` (module
   `Langlands.AlgebraicGeometry.Modules.RelativeAbelianSheafCohomologyPullbackProof`) proves
   `RelativeAbelianSheafCohomologyPullbackStatement.{u}`.

The theorem applies the first result to the second.

## Provenance

This is an internal assembly of Library results; no external theorem is transcribed. The
reduction in step 1 comes from Task 5898. The relative comparison in step 2 is the target of
Task 6104, proved through the derived sections/Hom comparison.
