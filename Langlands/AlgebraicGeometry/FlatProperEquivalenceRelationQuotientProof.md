# Effective quotients by flat proper equivalence relations (proof)

This module proves the published statement
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientStatement`. It contains no `sorry` and no new
axioms. The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Theorem

`Langlands.AlgebraicGeometry.flatProperEquivalenceRelationQuotient :
FlatProperEquivalenceRelationQuotientStatement.{u}`.

Let `A` be a noetherian ring and `p : Z ⟶ Spec A` H-quasi-projective. Then every flat proper
equivalence relation `s, t : R ⟶ Z` over `Spec A` has an effective quotient `π : Z ⟶ Q` with `Q`
H-quasi-projective over `Spec A` and `π` flat, surjective, proper and locally of finite
presentation, and `R` is the fibre product `Z ×_Q Z` (Altman–Kleiman; Nitsure, *Construction of
Hilbert and Quot schemes*, Theorem 6.8).

## Proof

The proof is one line. It applies the Library theorem
`FlatEquivalenceRelation.flatProperEquivalenceRelationQuotient_of_hilbertScheme`, which proves
`FlatProperEquivalenceRelationQuotientReductionStatement`, that is
`HilbertSchemeUniversalFamilyStatement.{u} → FlatProperEquivalenceRelationQuotientStatement.{u}`,
to the Library theorem `HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily`, which proves
`HilbertSchemeUniversalFamilyStatement.{u}`.

## Dependencies outside Mathlib

Library modules `Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof`
(the reduction) and `Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof`
(the Hilbert scheme with its universal family).
