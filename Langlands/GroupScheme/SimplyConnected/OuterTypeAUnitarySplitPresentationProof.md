# Proof: outer type A groups are special unitary groups when unitary algebras split

Module: `Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitPresentationProof`.

The theorem `Langlands.GroupScheme.outerTypeAUnitarySplitPresentation` proves the
published proposition `Langlands.GroupScheme.OuterTypeAUnitarySplitPresentationStatement.{u}`
at every universe `u`. It has no hypotheses. The statement and its Markdown are
imported unchanged. The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## What is proved

Let `K` be a field in which every central simple algebra with a unitary involution
splits (`UnitaryInvolutionSplitting K`). Let `G` be a simply connected,
absolutely almost-simple group over `K` of outer type `A_n`. Then `G` is the
special unitary group of a nonsingular Hermitian matrix of size `n + 1` over its
quadratic star field, presented on every test scheme by actual matrices. The
statement Markdown gives the exact form of this conclusion. The field and its
characteristic are arbitrary.

## The proof

The proof is a term that composes three published results.

1. `SpecialLinearTorusAutomorphism.specialLinearTorusAutomorphism`, in module
   `Langlands.GroupScheme.Reductive.SpecialLinearTorusAutomorphismProof`, proves
   `SpecialLinearTorusAutomorphismStatement.{u}`. A torus-preserving automorphism
   of the split special linear group with a split pinning is conjugation by a
   matrix over the base field when its based-root action is trivial. Otherwise it
   is conjugation by a matrix composed with inverse transpose.
2. `specialLinearTitsCocycle_of_torusAutomorphism`, in module
   `Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleReduction`,
   turns that result into `SpecialLinearTitsCocycleStatement.{u}`. This statement
   gives a finite Galois splitting extension, a local isomorphism from the split
   special linear group, and Galois discrepancy matrices with the inner or outer
   formula according to the Tits star action.
3. `OuterTypeAUnitarySplit.outerTypeAUnitarySplitPresentation_of_specialLinearTitsCocycle`,
   in module `Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitReduction`,
   proves `SpecialLinearTitsCocycleStatement.{u} → OuterTypeAUnitarySplitPresentationStatement.{u}`.
   The discrepancy matrices on the fixing group of the star field form a twisted
   projective cocycle. Unitary splitting gives a coordinate change that makes them
   scalar. The outer discrepancy then yields a nonsingular Hermitian matrix `J`
   over the star field. Galois descent identifies `G` with the special unitary
   group of `J`.

The module adds no other declarations.

## Constraints of the task

The proof does not assume any of the following statements, and no proof it uses
assumes them: `LocalAnisotropicSimplyConnectedClassificationStatement`,
`LocalRankOneClassificationStatement`, `LocalRankOneTitsIndexStatement`,
`LocalAnisotropicTypeAInnerStatement`, `LocalOuterTypeAHermitianModelStatement`,
or any local Kneser–Tits statement. Some of these statements are defined in
modules that the import closure contains, because those modules also hold shared
definitions. They occur there only as definitions, never as premises. The theorem
has no hypotheses, so it relies on no unproved statement.
