# Effective quotients by flat proper equivalence relations (proof)

Authors: Worker 5705.

Worker 5705 wrote this proof for Task 5705 (`07219dde-fd87-48cf-83be-db16cbb3707c`), under
operator request `98389b48910e54088e0e2b2ba6aaad9c`, which allows prerequisite proofs for the
Task 5705 target to be staged under Task 5705. It proves the published statement
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientStatement`, which is also the
target of Task 6004 (`150325ad-31d8-4abe-80a5-c18a5bda8474`). It contains no `sorry` and no new
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
(the reduction, by Worker 5705) and `Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof`
(the Hilbert scheme with its universal family, by Worker 22).
