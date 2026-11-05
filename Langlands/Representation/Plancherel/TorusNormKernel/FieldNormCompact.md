# Compactness of bounded-norm sets in a finite field extension

Author: Worker 1505.

This is a derived helper for the
[torus norm-kernel compactness proof](../TorusNormKernelCompactnessProof.md).
Declarations are in the namespace `Langlands.Plancherel.TorusNormKernel`.

Let `F` be a nontrivially normed field and `E` a finite field extension of `F`
(`FiniteDimensional F E`), carrying a topology with `IsModuleTopology F E`.
No completeness or valuation hypothesis is used except where `ProperSpace F` is
stated.

- `coordinateHomeomorph : E ≃ₜ (Fin (finrank F E) → F)` is the coordinate
  equivalence of the chosen basis `Module.finBasis F E`. Both directions are
  linear maps out of module-topology modules, so they are continuous
  (`IsModuleTopology.continuous_of_linearMap`). `coordinateHomeomorph_apply`
  and `coordinateHomeomorph_symm_apply` record the underlying linear maps.
- `t2Space_of_moduleTopology`: `E` is Hausdorff, because it embeds into
  `Fin d → F`.
- `continuous_algebraNorm`: `Algebra.norm F : E → F` is continuous. The norm
  is the determinant of `Algebra.leftMulMatrix` (`Algebra.norm_eq_matrix_det`).
  Each matrix entry `x ↦ b.repr (x * b j) i` is a linear functional, and the
  determinant is a polynomial in the entries (`Continuous.matrix_det`).

Assume moreover `ProperSpace F`.

- `isCompact_algebraNorm_le M`: `{x : E | ‖Algebra.norm F x‖ ≤ M}` is compact.
  In coordinates, `ν v = Algebra.norm F (e.symm v)` satisfies
  `ν (c • v) = c ^ d * ν v`, where `d = finrank F E > 0`
  (`Algebra.norm_algebraMap`), and vanishes only at `0`
  (`Algebra.norm_eq_zero_iff`). Fix `c` with `1 < ‖c‖`. The shell
  `K = {v | 1/‖c‖ ≤ ‖v‖ ≤ 1}` is compact. If it is nonempty, `‖ν‖` attains a
  positive minimum `m` on it. For `v ≠ 0`, `rescale_to_shell_zpow` gives `n`
  with `c ^ n • v ∈ K`. With `r = ‖c ^ n‖⁻¹`, this yields `‖v‖ ≤ r` and
  `r ^ d * m ≤ M`, hence `‖v‖ ≤ max 1 (M / m)`. If the shell is empty, every
  point of the set is `0`. The set is closed and bounded in the proper space
  `Fin d → F`, hence compact; its image under `e.symm` is the required set.
- `isCompact_algebraNorm_eq_one`: the closed subset of norm-one elements is
  compact.
- `isCompact_units_algebraNorm_eq_one`: `{u : Eˣ | ‖Algebra.norm F u‖ = 1}` is
  compact in the units topology. `E` is a Hausdorff topological ring
  (`IsModuleTopology.isTopologicalRing`), so `Units.embedProduct` is a closed
  embedding (`Units.isClosedEmbedding_embedProduct`). The set is closed, and it
  lies in the preimage of the compact product of the norm-one sets of `E` and
  `Eᵐᵒᵖ`, because `Algebra.norm F (u⁻¹) = (Algebra.norm F u)⁻¹`.

Provenance: internal derived infrastructure, built from Mathlib's field norm,
module topology and shell-rescaling lemmas. It cites no literature.
