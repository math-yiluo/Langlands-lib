# Local sums of the open-cell majorant

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCellLocalSum`, namespace
`Langlands.Global.CuspidalPairEisenstein.OpenCellMajorant`.

Let `v` be a finite place of the number field `F`, `F_v` its completion (`FiniteCompletion F v`),
`𝒪_v` its ring of integers and `q = N(v) = Ideal.absNorm v.asIdeal` the cardinality of the
residue field. For an `a × b` matrix `y` over `F_v` let `‖y‖` be the maximum of the norms of its
entries. The module proves that the sum of `max(1, ‖y‖)^(-β)` over the classes of
`M_(a×b)(F_v) / M_(a×b)(𝒪_v)` is at most `1 + 2 q^(a b - β)` when `β ≥ 0` and
`q^(a b - β) ≤ 1/2` (without a condition on `β` the sum can be infinite: for `β = 0` it counts
the classes). These sums are the local factors `localFactor` in the integral of the majorant of
[CuspidalPairEisensteinOpenCellMajorant.md](CuspidalPairEisensteinOpenCellMajorant.md).

## Content

- Norms on `F_v`: `absNorm_le_norm_of_one_lt` (a norm value `> 1` is at least `q`, since the
  norm of `F_v` takes values in `q^ℤ ∪ {0}`), `one_lt_absNorm`, `absNorm_pos`,
  `norm_le_one_of_lt_absNorm`; the uniformizer `uniformizer v` (the uniformizer unit of the
  Library's `p`-adic data of `F_v`) with `norm_uniformizer : ‖ϖ‖ = q⁻¹` and
  `uniformizer_ne_zero`.
- `entryNorm y`: the maximum norm of the entries of `y` (the sup norm of `y` viewed as a
  function `Fin a → Fin b → F_v`); `entryNorm_nonneg`, `norm_entry_le_entryNorm`,
  `entryNorm_le_iff`, `entryNorm_smul`, `entryNorm_neg`, `absNorm_le_entryNorm_of_one_lt`, and
  `max_one_entryNorm_add`: adding a matrix `o` with `‖o‖ ≤ 1` does not change `max(1, ‖y‖)`
  (ultrametric inequality).
- `integralLattice v` (the subgroup `Shahidi.integralMatrices` of matrices with entries in
  `𝒪_v`) and `MatrixQuotient v a b` (the quotient by it); `mem_integralLattice_iff`
  (`y` is integral iff `‖y‖ ≤ 1`).
- `classHeight v y`: `max(1, ‖y₀‖)` for the representative `y₀ = Quotient.out y`;
  `classHeight_mk` (it is `max(1, ‖z‖)` for every representative `z`), `one_le_classHeight`,
  `eq_zero_of_classHeight_le_one`, `classHeight_of_ne_zero` (for a nonzero class the height is
  `‖y₀‖ ≥ q`).
- `scaleMap v a b`: multiplication by `ϖ` on the quotient; `classHeight_scaleMap` (for `y ≠ 0`
  the height is divided by `q`), `scaleSection` with `scaleMap_scaleSection` (a set-theoretic
  section, multiplication of a representative by `ϖ⁻¹`).
- `kernelResidue`: the injection of the kernel of `scaleMap` into the matrices over the residue
  field, `y ↦ residue(ϖ y₀)`; `kernelResidue_injective`, the instance `finite_kernel`, and
  `card_kernel_le : #ker ≤ q^(a b)` (with `CompletionResidue.card_residueField`).
- **`tsum_comp_scaleMap_le`** (fibre bound): for `g ≥ 0` on the quotient,
  `∑_y g(ϖ y) ≤ #ker · ∑_z g(z)`.
- `truncatedTerm v β k y`: the term `max(1, ‖y‖)^(-β)` if `classHeight v y ≤ q^k` and `0`
  otherwise; for `β ≥ 0`, `ofReal_classHeight_rpow_le_one`, `truncatedTerm_zero_le`
  (`T_0(y) ≤ [y = 0]`) and `truncatedTerm_succ_le` (`T_(k+1)(y) ≤ [y = 0] + q^(-β) T_k(ϖ y)`);
  `tsum_truncatedTerm_le` (`∑_y T_k(y) ≤ 1 + 2 q^(a b - β)` for every `k`, for `β ≥ 0` with
  `q^(a b - β) ≤ 1/2`).
- **`tsum_classHeight_rpow_le`**: for `β ≥ 0` with `q^(a b - β) ≤ 1/2`,
  `∑_(y ∈ M(F_v)/M(𝒪_v)) max(1, ‖y‖)^(-β) ≤ 1 + 2 q^(a b - β)` (sums in `ℝ≥0∞`).

## Proofs

- `classHeight_scaleMap`: if `y ≠ 0`, then `‖y₀‖ ≥ q`, so `‖ϖ y₀‖ = q⁻¹ ‖y₀‖ ≥ 1` and the
  height of the class of `ϖ y₀` is `q⁻¹ ‖y₀‖`.
- `kernelResidue_injective`: if `ϖ y₀` and `ϖ y₀'` have the same residues, then
  `‖ϖ (y₀ - y₀')‖ < 1`, so every entry of `y₀ - y₀'` has norm `< q` and hence `≤ 1`; the classes
  agree.
- `tsum_comp_scaleMap_le`: `y ↦ (ϖ y, y - section(ϖ y))` injects the quotient into the product
  of the quotient with the kernel; summing `g` of the first coordinate over the product gives
  `#ker · ∑ g`.
- `tsum_truncatedTerm_le`, by induction on `k` with `ε = q^(a b - β)`: `T_0` is supported at
  `y = 0`, so its sum is at most `1 ≤ 1 + 2ε`. For the step, `truncatedTerm_succ_le` and the
  fibre bound give `∑ T_(k+1) ≤ 1 + q^(-β) q^(a b) (1 + 2ε) = 1 + ε (1 + 2ε) ≤ 1 + 2ε`,
  the last inequality because `ε ≤ 1/2`.
- `tsum_classHeight_rpow_le`: every finite partial sum is a partial sum of `T_K` for `K` large
  (`pow_unbounded_of_one_lt`), so the supremum of the partial sums is at most `1 + 2ε`.

## Provenance

The sums are the finite-place factors in the integral of the product majorant `Ω_β` of
[CuspidalPairEisensteinOpenCellMajorant.md](CuspidalPairEisensteinOpenCellMajorant.md), whose
finite integral yields the absolute convergence of the open-cell integral. In the formal proof
that integral takes the place of the convergent intertwining integrals that dominate the local
components of the Fourier coefficient in Shahidi, *On certain L-functions*, Amer. J. Math. 103
(1981) (`shahidi-1981-certain-l`), proof of Theorem 5.1, p. 352; the sums here are not Shahidi's
local intertwining integrals, and Shahidi does not write out such an estimate. The estimate
and the counting argument through truncations and the multiplication-by-`ϖ` fibre bound are
internal to the formal proof.
