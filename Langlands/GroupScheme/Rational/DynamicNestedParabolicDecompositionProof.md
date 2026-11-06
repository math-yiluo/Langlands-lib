# The all-test nested semistandard parabolic decomposition

This module proves `Langlands.GroupScheme.DynamicNestedParabolicDecompositionStatement`
(module `Langlands.GroupScheme.Rational.DynamicNestedParabolicDecompositionStatement`) with no
additional hypotheses, as the theorem `Langlands.GroupScheme.dynamicNestedParabolicDecomposition`
at the statement's universe `u`.

## Proof

The proof is a single application of two Library results.

- `Langlands.GroupScheme.dynamicNestedParabolicDecomposition_of_negation`
  (module `Langlands.GroupScheme.Rational.RootSignUnipotentInclusion`) proves
  `DynamicNestedParabolicDecompositionFromNegation`, that is,
  `RelativeRootNegationStatement → DynamicNestedParabolicDecompositionStatement`. Compatibility
  writes the two cocharacters as `zeta`, `eta` of a common maximal split torus with
  `P(zeta) ≤ P(eta)`. Then every actual relative root nonnegative on `zeta` is nonnegative on
  `eta` (`Dynamic.latticePairing_nonneg_of_parabolic_le`). Applying this to `-α`, which is again
  a relative root by negation stability, shows that every relative root positive on `eta` is
  positive on `zeta`. The positive-root criterion `Dynamic.unipotent_le_of_positive_rootSigns`,
  applied to `eta` and `zeta` in that order, then gives `U(eta) ≤ U(zeta)`
  (`Dynamic.unipotent_le_of_parabolic_le_of_negation`). Together with `P(zeta) ≤ P(eta)` and the
  centralizer inclusion `Z(zeta) ≤ Z(eta)` from compatibility, this gives the nested
  decomposition (`Dynamic.nestedLeviDecomposition_of_inclusions`). Here `P`, `Z` and `U` are the
  dynamic parabolic, centralizer and unipotent subgroup functors of the composite of each
  cocharacter with the torus inclusion.
- `Langlands.GroupScheme.relativeRootNegation`
  (module `Langlands.GroupScheme.Rational.RelativeRootNegationProof`) proves
  `RelativeRootNegationStatement` unconditionally: the actual relative roots of a maximal split
  torus in a connected reductive group over any field are stable under negation.

Applying the first to the second yields the statement.

## Provenance

This is internal assembly work. The reduction is the published Library theorem from task
a26bb091 (candidate 2dcd46b9); the negation theorem is the published proof from task 710252c7
(Worker 1310 and coauthors).
