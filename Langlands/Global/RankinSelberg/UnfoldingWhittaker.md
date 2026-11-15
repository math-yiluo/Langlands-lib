# Unitriangular and generic-character facts for the unfolding

Internal helper module for `UnequalUnfoldingReduction.md`.
Provenance: internal.

- `mem_blockUnipotentSubgroup_upperUnipotentWeight_iff`,
  `mem_unipotentAdelic_iff`, `mem_rationalPoints_upperUnipotent_iff`:
  the Library's `upperUnipotent` subgroup consists exactly of the upper
  unitriangular matrices, adelically and rationally.
- `unitriangularUnit`: a unitriangular matrix as an invertible matrix.
- `compactSpace_unipotentRationalQuotient`: `N_n(F) \ N_n(𝔸)` is
  compact, from the Library's rational reduction of adelic
  unitriangular matrices into a compact set
  (`PrimitiveAdelicHeight.exists_isCompact_unitriangular_reduction`).
- `superdiag_mul_of_isUnitriangular`: superdiagonal entries add under
  multiplication of unitriangular matrices.
- `isUnitriangular_of_mem_unipotentAdelic`, `genericCharacter_mul`,
  `genericCharacter_rational`, `norm_genericCharacter`,
  `continuous_genericCharacter`, `genericCharacter_inv`: the Library's
  `genericCharacter` is a character of `N_{r+1}(𝔸)`, trivial on
  `N_{r+1}(F)` when `ψ` is trivial on `F`, of absolute value one and
  continuous for unitary continuous `ψ`, and the character of `ψ⁻¹` is
  its complex conjugate.
- `continuous_evaluate`, `evaluate_rational_mul`: evaluation of a
  continuous rational-invariant function is continuous and left
  invariant under rational points.
