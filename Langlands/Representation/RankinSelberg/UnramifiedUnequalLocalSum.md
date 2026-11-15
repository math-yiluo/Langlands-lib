# The unramified unequal-rank local sum

Module `Langlands.Representation.RankinSelberg.UnramifiedUnequalLocalSum`, namespace
`Langlands.RankinSelberg.UnramifiedUnequalLocalSum`.

## Content

Fix ranks `t < r`, a natural number `q` (the residue cardinality), Satake parameters
`a : Fin (r + 1) → ℂˣ` of `GL_(r+1)` and `b : Fin (t + 1) → ℂˣ` of `GL_(t+1)`, and `s : ℂ`.
Weights of `GL_(t+1)` are `λ : Fin (t + 1) → ℤ`, standing for the torus element
`ϖ^λ = diag(ϖ^(λ_0), …, ϖ^(λ_t))`.

- `padZeroWeight r λ : Fin (r + 1) → ℤ` extends `λ` by `r - t` zeros. It is the weight of
  `diag(ϖ^λ, 1_(r-t))`, the image of `ϖ^λ` under the block embedding
  `g ↦ diag(g, 1_(r-t))` of `GL_(t+1)` into `GL_(r+1)`.
  Basic facts: `padZeroWeight_of_lt`, `padZeroWeight_of_le`, `antitone_padZeroWeight` (a
  partition stays antitone after padding), `antitone_nonneg_of_antitone_padZeroWeight` (if
  `t < r` and the padded weight is antitone, then `λ` is antitone with nonnegative entries),
  `sum_mul_padZeroWeight`, and `sum_halfModulus_padZeroWeight`, which says
  `∑_(i ≤ r) (r - 2i) λ'_i = ∑_(i ≤ t) (t - 2i) λ_i + (r - t) ∑_i λ_i` for `λ' = padZeroWeight r λ`.
- `localTerm q a b s λ` is the complex number
  `q^(∑_i (t - 2i) λ_i) · W°_a(λ') · W°_b(λ) · exp((s - (r - t)/2) · log(q^(-∑_i λ_i)))`,
  where `W°_a(λ')` is `halfModulus q λ' · satakeSchur a λ'` if `λ'` is antitone and `0`
  otherwise, and likewise `W°_b(λ)`. The four factors are, in order:
  `δ_B⁻¹(ϖ^λ)` for the upper Borel subgroup of `GL_(t+1)` (`∑_(i<j)(λ_i - λ_j)` equals
  `∑_i (t - 2i) λ_i`); Shintani's spherical Whittaker function of `GL_(r+1)` at
  `diag(ϖ^λ, 1_(r-t))`; that of `GL_(t+1)` at `ϖ^λ`; and `|det ϖ^λ|^(s - (r-t)/2)` with
  `|det ϖ^λ| = q^(-∑_i λ_i)`. For `|det|` the exponential form matches the Library's
  `detPower n g s = exp(s · log(detNorm g))`.
- `localTerm_eq_sphericalWhittaker`: over any field `F` with a valuation `v`, uniformizer
  `ϖ` and characters `θ`, `θ'` of the upper unipotent subgroups of `GL_(r+1)(F)` and
  `GL_(t+1)(F)` that are trivial on integral points (`IsIntegrallyTrivial v`), the two middle
  factors are the Library's `sphericalWhittaker hϖ θ q a (torus ϖ λ')` and
  `sphericalWhittaker hϖ θ' q b (torus ϖ λ)`. This is the Library's
  `sphericalWhittaker_torus` applied twice.
- `satakeSchur_padZeroWeight` and `satakeSchur_natWeight'`: on a natural partition
  `α : Fin (t + 1) → ℕ` the Schur values `satakeSchur a (padZeroWeight r α)` and
  `satakeSchur b α` equal the Jacobi–Trudi values `jacobiTrudiValue a α` and
  `jacobiTrudiValue b α`.
- `scalar_identity` and `localTerm_natWeight`: for `0 < q`, `t < r` and a natural partition `α`,
  `localTerm q a b s α = schurPairTerm a b (q^(-s)) α
  = s_α(a) · s_α(b) · (q^(-s))^|α|`. The powers of `q` cancel because
  `δ_B⁻¹ · δ_B^(1/2)(λ') · δ_B^(1/2)(λ) · |det|^(-(r-t)/2) = 1` on such weights, by
  `sum_halfModulus_padZeroWeight`.
- `norm_jacobiTrudiValue_le_rate`: the Library's bound `norm_jacobiTrudiValue_le` rewritten
  as `‖s_α(x)‖ ≤ C_x · (R_x^m)^|α|`, with `R_x = completeGrowthRate x = 1 + ∑_i ‖x_i‖`.
- `hasSum_schurPairTerm_of_growth`: the Cauchy identity with an explicit radius. If
  `R_x^(n+1) · R_y^(n+1) · ‖X‖ < 1`, then the Schur pair series over partitions with at most
  `n + 1` parts (the subtype `{α : Fin (n+1) → ℕ // Antitone α}`) converges absolutely, with
  sum `∏_j ∏_i (1 - x_i y_j X)⁻¹`.
- `hasSum_localTerm_of_growth`: for `0 < q` and `t < r`, if
  `R_a^(t+1) · R_b^(t+1) · ‖q^(-s)‖ < 1`, then the local terms over all weights
  `λ : Fin (t + 1) → ℤ` are absolutely summable (`Summable ‖localTerm q a b s ·‖`), and
  `HasSum (localTerm q a b s) (∏_i ∏_j (1 - a_i b_j q^(-s)))⁻¹`, with `i` over `Fin (r + 1)`
  outside and `j` over `Fin (t + 1)` inside.
- `exists_hasSum_localTerm`: the uniform half-plane. Given `t < r` and real numbers `A`, `B`,
  there is `σ` such that for every natural `q > 1`, all `a`, `b` with `‖a_i‖ ≤ q^A` and
  `‖b_j‖ ≤ q^B`, and every `s` with `σ < Re s`, the two conclusions of
  `hasSum_localTerm_of_growth` hold. The value is
  `σ = (t + 1)(max A 0 + max B 0) + log K / log 2` with `K = ((r + 2)(t + 2))^(t+1)`, so `σ`
  depends only on `r`, `t`, `A`, `B`, and not on `q`, `a` or `b`. This uniformity is what the
  global argument needs: there the half-plane is chosen before the place `v`, and the Satake
  bounds `‖α‖ ≤ q_v^C` of a spectral presentation have exactly this form.

## Provenance

This module is internal supporting material for the proof of the Library statement
`Langlands.Global.RankinSelbergGlobal.UnequalEulerFactorizationStatement`. It is the local
computation at an unramified place in Cogdell 2004 (Analytic theory of L-functions for GL_n,
Chapter 9 of Bernstein–Gelbart, An Introduction to the Langlands Program), §3, Theorem 3.3,
printed p.215: for unramified `π`, `π'` of `GL_n`, `GL_m` with `m < n` and `W°`, `W'°` the
normalized spherical Whittaker functions, `Ψ(s; W°, W'°) = L(s, π × π') =
det(I - q^(-s) A_π ⊗ A_π')⁻¹`. The standard computation behind it uses the Iwasawa
decomposition, Shintani's formula and the Cauchy identity. In the global proof,
the one-place cell decomposition of the Whittaker quotient measure
(`WhittakerCellDecompositionStatement`, a separate candidate) supplies the weights
`δ_B⁻¹(ϖ^λ)`, and the global Whittaker factorization at `v`
(`UnramifiedWhittakerFactorizationStatement`, also a separate candidate) supplies the values
`W°(ϖ^λ)`. What remains is the purely scalar identity
`∑_λ localTerm q a b s λ = ∏_(i,j) (1 - a_i b_j q^(-s))⁻¹` proved here, with its uniform
half-plane.

`padZeroWeight` and `localTerm` are derived definitions: they write out the cell weight of
`diag(ϖ^λ, 1_(r-t))` and the integrand of the local integral at `ϖ^λ`, using the Library's
`halfModulus`, `satakeSchur` and, by `localTerm_eq_sphericalWhittaker`, the Library's
`sphericalWhittaker`. The explicit radius in `hasSum_schurPairTerm_of_growth` and the uniform
`σ` in `exists_hasSum_localTerm` are not in the source, which only asserts convergence for
`Re s` large. The Library's `exists_schurCauchy_radius` gives a radius that depends on the
parameters without an explicit form, so it cannot give a half-plane uniform in `v`.

## Proof

- Padding lemmas: case analysis on `i < t + 1`. The sum identity reindexes sums over `Fin` by
  `Finset.range` (`Fin.sum_univ_eq_sum_range`) and drops the zero terms
  (`Finset.sum_subset`).
- `satakeSchur_padZeroWeight`: the Library's `satakeSchur_eq_eval_jacobiTrudi` (for antitone
  weights with nonnegative entries) and `jacobiTrudi_eq_jacobiTrudiIn`, then the padding
  invariance `jacobiTrudiIn_padWeight` of the Jacobi–Trudi determinant after identifying
  `padZeroWeight r α` with `padWeight α (r - t)` along `Fin.cast` (the reused `UnramifiedPairTorus.jacobiTrudiIn_cast` and
  `UnramifiedPairTorus.padWeight_apply` from `UnramifiedPairTorusCoefficient`).
- `scalar_identity`: writes every factor as `exp` of a multiple of `log q` and compares the
  exponents with `ring`. `localTerm_natWeight` unfolds the definitions, uses the two Schur
  lemmas and `sum_halfModulus_padZeroWeight`, and concludes by `linear_combination` from
  `scalar_identity`.
- `hasSum_schurPairTerm_of_growth`: absolute summability over all `α : Fin (n+1) → ℕ` from
  the Library's `summable_norm_schurPairTerm_of_bounds` with the rate bounds above, restricted
  to the antitone subtype. The value of the sum is the Library's
  `tsum_schurPairTerm_eq_seriesValue` followed by `seriesValue_complexCauchySeries`. The
  needed bounds `‖x_i y_j X‖ < 1` follow from `‖x_i‖ ≤ R_x ≤ R_x^(n+1)`.
- `hasSum_localTerm_of_growth`: the map `α ↦ (α_i : ℤ)` from natural partitions into weights is
  injective. Outside its range the local term vanishes: a nonzero term has antitone padded
  weight, and then `antitone_nonneg_of_antitone_padZeroWeight` writes the weight as a
  natural partition. `Function.Injective.hasSum_iff` and `summable_iff` transfer the
  conclusions of `hasSum_schurPairTerm_of_growth` through `localTerm_natWeight`.
  `Finset.prod_comm` reorders the product.
- `exists_hasSum_localTerm`: for `q ≥ 2` with `L = log q ≥ log 2`, the bound `‖z_i‖ ≤ q^C`
  gives `R_z ≤ (k + 2) · exp(max C 0 · L)` for `z` of length `k + 1`. Hence
  `R_a^(t+1) R_b^(t+1) ‖q^(-s)‖ ≤ exp(log K + ((t+1)(A' + B') - Re s) L)`, and the exponent is
  negative because `Re s - (t+1)(A' + B') > log K / log 2 ≥ log K / L`.
