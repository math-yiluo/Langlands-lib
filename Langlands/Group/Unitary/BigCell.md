# The big cell of `U(ν, ν)`

The module `Langlands.Group.Unitary.BigCell` describes the big cell `P w P` of the quasi-split
unitary group `U(ν, ν)` (`P` the Siegel parabolic subgroup, `w` the Weyl element), shows that every
finite set has a translate into it, deduces that `P` and `w` generate the group, and gives a
criterion for a subgroup to be open.

## Content

Let `E / F` be fields with `c : E →ₐ[F] E` and `U(ν, ν) = UnitaryGroup.ofForm c (hyperbolicForm ν E)`
(`Langlands/Group/Unitary/Hyperbolic.lean`).

- `isInBigCell_iff_det_ne_zero`: `g = [[A, B], [C, D]]` lies in `P w P` exactly when `det C ≠ 0`.
  If `g = p w q` the lower left block of `g` is a product of invertible blocks. Conversely,
  `v = C⁻¹ D` is Hermitian (from the unitarity relations `C c(D)ᵀ = D c(C)ᵀ`), and
  `g [[1, -v], [0, 1]] w⁻¹` lies in `P`.
- `exists_mul_isInBigCell`: for a quadratic involution `c` (`IsQuadraticInvolution c δ`) and `F`
  infinite, every finite subset of `U(ν, ν)` has a common right translate `g u` into `P w P`, with
  `u = [[1, 0], [t, 1]]` for a Hermitian `t`. For one `g`, a Hermitian `t` with `C + D t`
  invertible exists: after a change of variables with the skew-Hermitian `δ · 1`, this is a
  statement about pairs `(A, C)` with `Aᵀ S c(C) + Cᵀ S c(A) = 0` and no common kernel, proved by
  induction on `dim ker A`, adding rank-one corrections (internal lemmas `transv_kills`,
  `transv_step`, `transv_field`, `exists_herm_transverse`). For finitely many `g`, the determinant of
  `C + D (t₀ + r (t₁ - t₀))` is a non-zero polynomial in `r ∈ F`, so all but finitely many `r` work
  (`finite_det_line_zero`, `exists_herm_transversal`).
- `IsInBigCell.mem_of_le`, `eq_top_of_siegelParabolic_le_of_weylElement_mem`: a subgroup containing
  `P` and `w` contains `P w P`, hence every `g` (`g = (g u) u⁻¹` with `u`, `g u` in the big cell),
  so `P` and `w` generate `U(ν, ν)`.
- `isOpen_of_eventually_mem_siegelParabolic`: for a Hausdorff topological field `E` (with the
  topology of `U(ν, ν) ⊆ GL_{2ν}(E)` induced from matrices), a subgroup `U` which contains the
  elements of `P` near `1` and the conjugates `w⁻¹ p w` of the elements `p` of `P` near `1` is open.
  Near `1`, the lower right block `D` of `g` is invertible, and
  `g = (g k⁻¹) k` with `k = w⁻¹ [[1, -D⁻¹C], [0, 1]] w`, both factors tending to `1` with `g`
  and lying in `P` and `w⁻¹ P w`.

These are the group-theoretic facts of the construction of the Leray splitting of `U(ν, ν)`: the representation
is defined on `P` and at `w` and extended by `Langlands/Group/BigCellHom.lean`, and its smoothness is
checked on `P` and `w⁻¹ P w` (`Langlands/Theta/DualPair/Unitary/Splitting.lean`).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, files under
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/`: `InCellIffDetNeZero.lean`,
`ExistsHermitianSplitUnitaryLowerBlockInvertible.lean`, `ExistsTranslateInCell.lean`,
`SiegelParabolicWeylElementGenerateUnitary.lean`, `IsOpenSubgroupOfSiegelAndOppositeNhds.lean`
(each whole, without the import and `open` lines). The repository has no licence file; the text is
used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `GlobalTheory.KSp`, `KSp.OpenCrit` → `Langlands.UnitaryGroup` (public) and
  `Langlands.UnitaryGroup.BigCell.Internal`.
- Renamed: `inCell_iff_det_ne_zero` → `isInBigCell_iff_det_ne_zero`, `exists_translate_inCell` →
  `exists_mul_isInBigCell`, `mem_of_inCell` → `IsInBigCell.mem_of_le`, `sieg_weyl_generate` →
  `eq_top_of_siegelParabolic_le_of_weylElement_mem`, `isOpen_of_sieg_of_opp` →
  `isOpen_of_eventually_mem_siegelParabolic`; the helpers are internal.
- Hypotheses: `[CharZero F]` → `[Infinite F]` where an element of `F` outside a finite set is chosen,
  and dropped elsewhere; the quadratic involution only where it is used (`δ` with `c δ = -δ`); the
  open-subgroup criterion is stated for any Hausdorff topological field `E` with continuous
  inversion, instead of a quadratic extension of a nonarchimedean local field with its module
  topology (the source obtained these properties from that hypothesis). Types in any universe.
- The four wrappers `…Statement.lean` of these results are not taken.

## Declarations

- `UnitaryGroup.isInBigCell_iff_det_ne_zero`
- `UnitaryGroup.exists_mul_isInBigCell`
- `UnitaryGroup.IsInBigCell.mem_of_le`
- `UnitaryGroup.eq_top_of_siegelParabolic_le_of_weylElement_mem`
- `UnitaryGroup.isOpen_of_eventually_mem_siegelParabolic`

All in the namespace `Langlands`.

## Dependencies

`Langlands.Group.Unitary.Hyperbolic`; Mathlib: `Algebra.Polynomial.Roots`,
`LinearAlgebra.Matrix.Polynomial`, `LinearAlgebra.Matrix.ToLinearEquiv`,
`Topology.Algebra.Ring.Basic`, `Topology.Instances.Matrix`, `Topology.Algebra.OpenSubgroup`,
`Topology.Algebra.Group.Units`, `Tactic.Group`, `Tactic.Abel`.
