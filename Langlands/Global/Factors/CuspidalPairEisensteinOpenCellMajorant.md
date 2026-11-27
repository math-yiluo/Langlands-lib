# A product majorant on the adelic matrices with finite integral

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCellMajorant`, namespace
`Langlands.Global.CuspidalPairEisenstein.OpenCellMajorant`.

On the adelic `(t + 1) × (r + 1)` matrices `M(𝔸) = M_((t+1)×(r+1))(𝔸)` the module defines

`Ω_β(Y) = (1 + ‖Y_∞‖)^(-β) · ∏_(v finite) max(1, ‖Y_v‖)^(-β)`,

where `Y_∞` is the vector of archimedean coordinates of the entries of `Y` (in the mixed space
`ℝ^(r₁) × ℂ^(r₂)` of `F`, with its sup norm) and `‖Y_v‖` is the maximum norm of the entries
of the component `Y_v` at the finite place `v`; almost all factors of the product are `1`. It
proves that the lower integral `∫⁻ Ω_β dμ` is finite for every additive Haar measure `μ` on `M(𝔸)` (Borel σ-algebra) once
`β` exceeds both the real dimension `d` of the archimedean coordinates and
`(t + 1)(r + 1) + 1`. The local sums are those of
[CuspidalPairEisensteinOpenCellLocalSum.md](CuspidalPairEisensteinOpenCellLocalSum.md); the
decomposition into cells is that of
[CuspidalPairEisensteinOpenCellExhaustion.md](CuspidalPairEisensteinOpenCellExhaustion.md).

## Content

- `flatten F a b`: the continuous additive equivalence of adelic `a × b` matrices with adelic
  row vectors of length `a b` (`finProdFinEquiv`).
- `norm_le_one_iff_mem_integers`: `‖x‖ ≤ 1` iff `x ∈ 𝒪_v`.
- `archWeight β Y = (1 + ‖Y_∞‖)^(-β)`, `localWeight β v Y = max(1, ‖Y_v‖)^(-β)`,
  `finiteWeight β Y = ∏ᶠ_v localWeight β v Y`, `majorant β Y = archWeight β Y · finiteWeight β Y`;
  positivity (`localWeight_pos`, `archWeight_pos`, `finiteWeight_pos`, `majorant_pos`),
  `entryNorm_matrixComponent_le_one`, `localWeight_eq_one` (the local weight is `1` where `Y` is
  integral), `mulSupport_localWeight_finite`, and `finiteWeight_eq_one_of_mem` (the finite weight
  is `1` on the set `U_∅` of matrices integral at every finite place).
- Translation by a matrix supported at one place `v` (`OpenCellExhaustion.localMatrix`):
  `archWeight_localMatrix_add` (no change), `localWeight_localMatrix_add`,
  `finiteWeight_localMatrix_add` and `majorant_localMatrix_add`: if `Z` is integral at `v`, then
  `Ω_β(localMatrix v y₀ + Z) = classHeight(y)^(-β) Ω_β(Z)` for the representative `y₀` of a class
  `y ∈ M(F_v)/M(𝒪_v)`.
- `localFactor r t β v = ∑_(y ∈ M(F_v)/M(𝒪_v)) max(1, ‖y‖)^(-β)` (in `ℝ≥0∞`).
- **`setLIntegral_cons`**: for a left invariant measure and `v ∉ A`,
  `∫_(U_(A ∪ {v})) Ω_β = localFactor v · ∫_(U_A) Ω_β`; **`setLIntegral_eq_prod`**:
  `∫_(U_A) Ω_β = (∏_(v ∈ A) localFactor v) ∫_(U_∅) Ω_β` for a left invariant measure;
  **`lintegral_eq_iSup`**: `∫ Ω_β = sup_A ∫_(U_A) Ω_β` for every measure (lower integrals, no
  measurability of `Ω_β` is needed).
- `matrixSplit F a b`: `flatten` followed by `EqualAnalytic.rowSplit`, the splitting into
  archimedean and finite-adelic coordinates; `integralRows`, the compact set of finite-adelic
  rows with integral entries (`isCompact_integralRows`), `matrixSplit_snd_mem`, `archWeight_eq`.
- **`setLIntegral_empty_lt_top`**: for every additive Haar measure `μ`, if `d < β`, then
  `∫_(U_∅) Ω_β dμ < ∞`.
- `two_le_absNorm`: `N(v) ≥ 2`.
- Let `D = (t + 1)(r + 1)`. Each of the following three results assumes `β > D + 1`:
  `localFactor_le` (`localFactor v ≤ 1 + 2 N(v)^(D - β)`), `summable_localExponent`
  (`∑_v N(v)^(D - β) < ∞`), and `prod_localFactor_le`
  (`∏_(v ∈ A) localFactor v ≤ exp(2 ∑_v N(v)^(D - β))` for every finite set `A` of places).
- **`lintegral_majorant_lt_top`**: for every additive Haar measure `μ`, if
  `d < β` and `D + 1 < β`, then `∫⁻ Ω_β dμ < ∞`.

## Proofs

- `setLIntegral_cons`: `U_(A ∪ {v})` is the disjoint countable union of the cells
  `localMatrix v y₀ + U_A` (`OpenCellExhaustion.iUnion_cell`, `pairwise_disjoint_cell`,
  `measurableSet_cell`); on each cell, translation invariance of `μ` and
  `majorant_localMatrix_add` give `classHeight(y)^(-β) ∫_(U_A) Ω_β`.
- `setLIntegral_eq_prod`: induction on `A`.
- `lintegral_eq_iSup`: the sets `U_A` are measurable, directed and cover `M(𝔸)`
  (`OpenCellExhaustion.exists_mem_integralOutside`); continuity from below of the measure with
  density `Ω_β`.
- `setLIntegral_empty_lt_top`: the image of `μ` under the homeomorphic additive equivalence
  `matrixSplit` is an additive Haar measure on `(F_∞)^D × (𝔸_f)^D`, hence a constant multiple of
  the product of Lebesgue measure and a Haar measure (`Measure.isAddLeftInvariant_eq_smul`). On
  `U_∅` the majorant is at most `(1 + ‖x_∞‖)^(-β) · 1_K(x_f)` with `K = integralRows` compact,
  so the integral is at most a constant times
  `∫ (1 + ‖x‖)^(-β) dx · Haar(K)` (`lintegral_prod_mul`), finite by
  `finite_integral_one_add_norm` for `d < β` and compactness of `K`.
- `localFactor_le`: `OpenCellMajorant.tsum_classHeight_rpow_le`, whose hypotheses follow from
  `β > D + 1`: `β ≥ 0`, and `N(v)^(D - β) ≤ N(v)^(-1) ≤ 1/2` because `N(v) ≥ 2`.
- `summable_localExponent`: `HeckeEulerProduct.summable_absNorm_rpow` with exponent
  `β - D > 1`.
- `prod_localFactor_le`: `1 + 2x ≤ exp(2x)` and `∑_(v ∈ A) ≤ ∑_v` for nonnegative terms.
- `lintegral_majorant_lt_top`: by `lintegral_eq_iSup` and `setLIntegral_eq_prod`, every
  `∫_(U_A) Ω_β` is at most `exp(2 ∑_v N(v)^(D - β)) · ∫_(U_∅) Ω_β`, which is finite.

## Provenance

For a section `φ` there is `b ∈ ℝ` such that, for `e = Re s + b ≥ 0`, a constant multiple of
`Ω_e` bounds the norm of the open-cell integrand of
[CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md) (see
[CuspidalPairEisensteinOpenCellPointwise.md](CuspidalPairEisensteinOpenCellPointwise.md)). The
finite lower integral of `Ω_e` for `e > max(d, D + 1)` proved here is the bound used to prove the
absolute convergence of that integral
([CuspidalPairEisensteinOpenCellConvergenceProof.md](CuspidalPairEisensteinOpenCellConvergenceProof.md)).
This parallels Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981)
(`shahidi-1981-certain-l`), proof of Theorem 5.1, p. 352, where the local components of the
Fourier coefficient are dominated by intertwining integrals that converge for `Re(s)` large. The
integral of `Ω_e` is not Shahidi's intertwining integral, and the product majorant, the
reduction of its integral to the local sums and to the integral of `(1 + ‖x‖)^(-β)` over the
archimedean coordinates are internal to the formal proof.
