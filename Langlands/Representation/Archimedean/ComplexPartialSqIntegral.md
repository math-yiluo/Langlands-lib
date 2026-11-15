# Integrability of products of partial square sums on `ℂ^m`

Lean module: `Langlands.Representation.Archimedean.ComplexPartialSqIntegral`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It sharpens the integrability estimate of
`ComplexParabolicChartBound` (which needs every exponent `< −1`) to the exact criterion for the
chart bound of a principal-series function. This is needed for Langlands-ordered lists with ties
(equal real parts of exponents), where some exponents equal `−1`.

Notation: `partialSq x l = 1 + ∑_{j<l} |x_j|²` for `x ∈ ℂ^m` (`ComplexParabolicChartBound.partialSq`;
written `r_l(x)` below). Declarations without a prefix are in the namespace
`Langlands.Archimedean.ComplexPartialSqIntegral`.

## The statement

`ComplexPartialSqIntegrableStatement`: for every `m` and real exponents `γ_0, …, γ_{m−1}` such that

`∑_{l ≥ j} (γ_l + 1) < 0` for every `j < m`,

the function `x ↦ ∏_{l<m} r_{l+1}(x)^{γ_l}` is integrable on `ℂ^m` (Lebesgue measure). The tail
sums are written `∑_l (if j ≤ l then γ_l + 1 else 0)`. It is proved as
`Langlands.Archimedean.complexPartialSqIntegrable`.

Provenance. Derived, internal infrastructure without a literature source: an elementary iterated
integral (the complex-rank-one case of the Gindikin–Karpelevich convergence criterion, made explicit
on the chart of the opposite unipotent radical of `P_{m,1}`). No literature claim.

## Proof

1. **One variable** (`integral_add_sq_rpow`, `integrable_add_sq_rpow`). For `A > 0`,
   `∫_ℂ (A + |t|²)^β dt = A^{β+1} ∫_ℂ (1 + |t|²)^β dt`, by the substitution `t = √A s`
   (`Measure.integral_comp_smul`; the real dimension of `ℂ` is `2`). For `β < −1` the function is
   integrable, by comparison with the scaled `(1 + |s|²)^β`
   (`ComplexParabolicChartBound.integrable_one_add_sq_rpow`, `Integrable.comp_smul`).
2. **Last coordinate** (`partialSq_snoc_castSucc`, `partialSq_snoc_last`). For `x = (y, t)` with
   `y ∈ ℂ^m`, `t ∈ ℂ`: `r_{l+1}(x) = r_{l+1}(y)` for `l < m` and `r_{m+1}(x) = r_m(y) + |t|²`.
3. **Induction** (`integrable_partialSq_mul_prod`). The stronger claim: if
   `δ + ∑_{l ≥ j} (γ_l + 1) < 0` for every `j` (`TailCondition γ δ`), then
   `y ↦ r_m(y)^δ ∏_{l<m} r_{l+1}(y)^{γ_l}` is integrable on `ℂ^m`. For `m = 0` the function is `1`
   on a one-point space of measure `1`. For `m + 1`, split `ℂ^{m+1} = ℂ × ℂ^m` (the last
   coordinate first; `MeasurableEquiv.piFinSuccAbove` at the last index, measure preserving). By
   step 2 the integrand is `(r_m(y) + |t|²)^{β} ∏_{l<m} r_{l+1}(y)^{γ_l}` with `β = δ + γ_m < −1`
   (the condition at `j = m`). By step 1 it is integrable in `t`, with integral
   `c_β r_m(y)^{β+1} ∏_{l<m} r_{l+1}(y)^{γ_l}`, and this is integrable in `y` by induction with
   `δ' = β + 1` (the condition for `δ'` and `γ_0, …, γ_{m−1}` is the old condition at the same
   `j`). Integrability on the product follows from `integrable_prod_iff'`.
4. The statement is the case `δ = 0` (`integrable_prod_partialSq`).

`tailCondition_of_le`: if every `γ_l ≤ −1` and the last exponent is `< −1`, the tail condition
holds. For the chart exponents `γ_l = Re e_{l+1} − Re e_l − 1` of a Langlands-ordered list, this is
the case where the last real part is strictly smaller than the previous one.
