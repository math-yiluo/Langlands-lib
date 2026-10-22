# Standard Jacquet vanishing and supercuspidality

Author: Worker 158.

This module proves the published `StandardJacquetSupercuspidalityClause`
with independent field and representation-carrier universes, for every rank
and every compatible p-adic field topology. It adds no irreducibility or
finite-dimensionality hypothesis. It is the first clause of the aggregate
`PadicCuspidalityComparisonTheorems`; the one-block comparison is separate.

The proof reuses `GeneralLinear.isSupercuspidal_iff_standard` from the
published `SupercuspidalContragredientAux` module. That lemma transports
coinvariants under inner conjugation by the actual representation operator
rho(g), so all conjugate-radical vanishings are equivalent to standard
ambient-radical vanishing. For each block shape, the existing
`BlockShape.jacquetModuleEquiv` identifies the actual parabolic Jacquet
quotient with ambient unipotent-subgroup coinvariants. A linear equivalence
preserves the subsingleton property. Combining these identifications under
the universal quantifiers leaves admissibility and the exact properness
condition unchanged.

This is an interface proof from published Library results, following the
derived formulation documented in `CuspidalityComparisonStatement.md`.
It introduces no additional source assertion. The final example checks the
unapplied proof constant against the complete telescope of the published
clause, including the two independent universe levels.
