# Admissibility and unitarity of normalized induction from actual rational parabolics

Author: Worker 5148. This is a supporting unit for proof task
`822bbd74-8853-4535-87b2-aede25e9a259` (Renard VI.8.5). It does not complete that task.

## Statements proved

The module proves two published closed propositions of
`Langlands/Representation/Exponents/MaximalLeviReducibilityUnitaryInputs.lean`, at
independent universes `u` (field) and `v` (carrier). Neither statement is changed.

- `leviInductionAdmissible : LeviInductionAdmissibleStatement.{u, v}`. For a nonarchimedean
  local field `k`, a connected reductive `G` over `k` with locally compact, nonarchimedean
  `G(k)`, and an actual rational parabolic `p : P ⟶ G` with rational Levi `l : M ⟶ P`,
  geometric unipotent radical `r : U ⟶ P` and `IsIso (subgroupMultiplication l r)`, the
  published normalized induction `leviInductionFunctor p l r hp hr hl hmul` sends every
  admissible smooth representation of `M(k)` to an admissible representation of `G(k)`.
  This is Renard III.2.3 for actual rational parabolics.
- `leviInductionUnitarizable : LeviInductionUnitarizableStatement.{u, v}`. In the same
  setting, `leviInductionFunctor` sends every smooth representation of `M(k)` whose
  underlying representation is unitarizable to a representation of `G(k)` whose underlying
  representation is unitarizable. This is Renard IV.2.3 for actual rational parabolics.

## Proof

Both proofs only apply published reductions to published proofs.

- `leviInductionAdmissible` applies `leviInductionAdmissible_of_quotientCompact`
  (`MaximalLeviReducibilityInductionInputs.lean`) to `arbitraryParabolicQuotientCompact`
  (`ArbitraryParabolicQuotientCompactProof.lean`), the proof of
  `ArbitraryParabolicQuotientCompactStatement`: `P(k)\G(k)` is compact.
- `leviInductionUnitarizable` applies `leviInductionUnitarizable_of_inputs` (same module)
  to four published proofs:
  - `RationalPointFamily.rationalReductiveUnimodularity`
    (`Aubert/General/RationalReductiveUnimodularityProof.lean`): rational points of
    connected reductive groups are unimodular, given standard cocharacters;
  - `GroupScheme.standardCocharacter` (`GroupScheme/Rational/StandardCocharacterProof.lean`);
  - `arbitraryParabolicQuotientCompact`;
  - `GroupScheme.parabolicRootPresentationExistence`
    (`GroupScheme/Rational/ParabolicRootPresentationProof.lean`).

  The reduction combines unimodularity of `G(k)` and `M(k)` with a root presentation of
  `P` to identify the modular character of `P(k)`, and with compactness of `P(k)\G(k)`
  builds the invariant form on the induced space.

No hypothesis is added; the only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## Use

These close inputs 4 and 5 of `genericInducedIrreducibility_of_statements`
(`Langlands/Representation/Families/RenardGenericIrreducibilityReduction.lean`), and the
corresponding premises of the VII.1.3 reduction
`MaximalLeviSupercuspidalReducibilityFromInputsProof.lean`.
