# Continuation of the real local Rankin–Selberg integrals from Jacquet's pair identity

Entry module of an intermediate result of Task 7400, towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. Authored by
Worker 823. Every declaration is proved, with no axioms beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

The module reduces the meromorphic continuation and the functional equation of the real local
Rankin–Selberg integrals, in both ranks, to an identity between absolutely convergent
integrals: Jacquet's pair identity. It combines three results:
- `mellinPairContinuation` (module `ArchimedeanMellinPair`), the core of Jacquet's
  Proposition 4.1;
- `realPairMellinFactor` (module `ArchimedeanRealPairFactor`), the existence of a rapidly
  decreasing Mellin pair for the Library's real pair factors;
- the convergence of the integrals on a right half-plane, which is a hypothesis here.

The conclusions are the continuation and functional-equation conjuncts of the Library's
`RealJacquet.UnequalEquation` and `RealJacquet.EqualEquation` (module
`RealJacquetConventionReduction`), with exactly their integrals, `L`-factors and `ε`-factor.

Notation: `mellin f s = ∫₀^∞ t^(s-1) f(t) dt` (Mathlib). `RapidDecay h` (module
`ArchimedeanMellinPair`) means that for every real `M` there is `C` with `‖h t‖ ≤ C t^M` for
all `t > 0`. For a class `q` in `N_(m)(ℝ) \ GL_m(ℝ)`, `g = q.out` is its chosen
representative.

## The pair identity

`ArchimedeanRealPairIdentity.PairIdentity μ μ' F δ F' δ' D Dd E sign` is the proposition: for
every real `B` and all measurable `h, k : ℝ → ℂ` with `RapidDecay h`, `RapidDecay k` and, for
every `s : ℂ`,
- `mellin h (-s) = sign · E(s) · exp(s² + B s) · D(s)`,
- `mellin k (s - 1) = exp(s² + B s) · Dd(1 - s)`,

one has `∫ F(x) h(δ(x)) dμ(x) = ∫ F'(x) k(δ'(x)) dμ'(x)`.

Two instances are defined. Below,
`L = (realPairLFactor ds es).denominator`, `Ld = (realPairLFactor dds ees).denominator` and
`ε(s) = realPairEpsilon ds es b (√|a|) _ s`, the factors of `UnequalEquation` and
`EqualEquation`. Also `quotientDetAbs q = |det g|` for `g = q.out`.

- `UnequalPairIdentity h a D W W' ds es dds ees b sign` (for `t < r`, so
  `m = t + 1 < n = r + 1`): `PairIdentity` with
  - `μ = D.measure` on `N_m \ GL_m(ℝ)`, `F = realUnequalIntegrand h W W' 0`, that is
    `F(q) = W(diag(g, 1_(n-m))) W'(g) |det g|^(-(n-m)/2)`, and `δ = quotientDetAbs`;
  - `μ' = realUnequalDualMeasure a D`, the product of `D.measure` and the rectangular measure
    on `M_((n-m-1) × m)(ℝ)`, `F' = realUnequalDualKernel h W W' 0`, that is
    `F'(q, x) = (ρ(w_(n,m)) W̃)([[g, 0, 0], [x, 1, 0], [0, 0, 1]]) W̃'(g) |det g|^(-(n-m)/2)`,
    and `δ'(q, x) = |det g|`;
  - `D = L`, `Dd = Ld`, `E = ε`.
- `EqualPairIdentity a b D W W' Φ ds es dds ees sign` (for `n = r + 1`): `PairIdentity` with
  `μ = μ' = D.measure`, `F = realEqualIntegrand W W' Φ 0`, that is
  `F(q) = W(g) W'(g) Φ(e_n g)`, `F' = realEqualIntegrand W̃ W̃' Φ̂ 0` with
  `W̃ = dualFunction (r + 1) W` and `Φ̂ = realFourierTransform b Φ`,
  `δ = δ' = quotientDetAbs`, and the same `D, Dd, E`.

So the pair identity says
`∫ W W' Φ(e_n g) h(|det g|) dg = ∫ W̃ W̃' Φ̂(e_n g) k(|det g|) dg` in equal rank, and the
analogous identity of the two unequal-rank integrals, for every pair `(h, k)` as above.

## The statement

`Langlands.Global.RankinSelbergGlobal.RealPairIdentityContinuationStatement : Prop` is the
conjunction of two statements.

**Unequal rank.** Let `r t : ℕ` with `h : t < r`, `a b : ℝˣ`, `D : RealQuotientMeasureData t`,
`W : GL_(r+1)(ℝ) → ℂ`, `W' : GL_(t+1)(ℝ) → ℂ`, block lists `ds es dds ees`, `sign : ℂ` and
`σ₀ : ℝ`. Assume:
1. `sign ≠ 0`;
2. `realUnequalIntegrand h W W' s` is `D.measure`-integrable whenever `σ₀ < Re s`;
3. `realUnequalDualKernel h W W' s` is `realUnequalDualMeasure a D`-integrable whenever
   `σ₀ < Re s`;
4. `UnequalPairIdentity h a D W W' ds es dds ees b sign`.

Then there are `σ : ℝ` and `M, Md : ℂ → ℂ`, meromorphic on `ℂ`, with
`realUnequalIntegral h D W W' s = M s` and `realUnequalDualIntegral h a D W W' s = Md s`
whenever `σ < Re s`. Moreover, for `s` outside a discrete closed subset of `ℂ` (the filter
`codiscrete ℂ`),
`L(s)⁻¹ · Md(1 - s) = sign · ε(s) · Ld(1 - s)⁻¹ · M(s)`.

**Equal rank.** Let `r : ℕ`, `a b : ℝˣ`, `D : RealQuotientMeasureData r`,
`W, W' : GL_(r+1)(ℝ) → ℂ`, `Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ`, block lists, `sign` and `σ₀`.
Assume `sign ≠ 0`, that `realEqualIntegrand W W' Φ s` and
`realEqualIntegrand W̃ W̃' Φ̂ s` are `D.measure`-integrable whenever `σ₀ < Re s`, and
`EqualPairIdentity a b D W W' Φ ds es dds ees sign`. Then the same conclusion holds for
`realEqualIntegral D W W' Φ` and `realEqualDualIntegral b D W W' Φ`.

These are the last five conjuncts of `UnequalEquation h a D W W' ds es dds ees b sign` and of
`EqualEquation a b D W W' Φ ds es dds ees sign`. The theorem
`Langlands.Global.RankinSelbergGlobal.realPairIdentityContinuation` proves the statement.

## Proof structure

All declarations except the last two are in the namespace
`Langlands.Global.RankinSelbergGlobal.ArchimedeanRealPairIdentity`.

### From the pair identity to the theta identity

- `ofReal_cpow_eq_exp`: `(x : ℂ)^z = exp(log x · z)` for `x > 0`.
- `rapidDecay_comp_mul_left`, `rapidDecay_const_mul`: `t ↦ h(c t)` for `c > 0` and `t ↦ c h(t)`
  are rapidly decreasing when `h` is.
- `theta_eq_of_pairIdentity`. Let `(h, k)` satisfy the formulas of `PairIdentity` with `B = 0`.
  For `a > 0` apply `PairIdentity` with `B = log a` to the scaled pair
  `h_a(t) = h(a t)`, `k_a(t) = a k(a⁻¹ t)`. By Mathlib's `mellin_comp_mul_left` and
  `mellin_const_smul`, `mellin h_a (-s) = a^s mellin h (-s)` and
  `mellin k_a (s - 1) = a · a^(s - 1) mellin k (s - 1) = a^s mellin k (s - 1)`. Since
  `a^s = exp((log a) s)`, the scaled pair satisfies the formulas with `B = log a`. The identity
  `∫ F h_a(δ) = ∫ F' k_a(δ')` is `θ(a) = a θ'(a⁻¹)`, where `θ = theta μ F δ h` and
  `θ' = theta μ' F' δ' k` (module `ArchimedeanMellinPair`). This is Jacquet's (4.1).

### Kernels of the form `K(s) = K(0) δ^s`

- `norm_kernel`: if `K(s)(x) = K(0)(x) δ(x)^s` with `δ > 0`, then
  `‖K(σ)(x)‖ = ‖K(0)(x)‖ δ(x)^σ` for real `σ` (Mathlib's
  `Complex.norm_cpow_eq_rpow_re_of_pos`).
- `kernel_zero_eq`: `K(0)(x) = K(s)(x) δ(x)^(-s)`.
- `exists_continuation_of_kernels`. Let `μ, μ'` be s-finite and `δ, δ'` measurable and
  positive. Let `K(s) = K(0) δ^s` and `Kd(s) = Kd(0) δ'^s` be integrable for `Re s > σ₀`, with
  `Z(s) = ∫ K(s) dμ` and `Zd(s) = ∫ Kd(s) dμ'` there. Assume `sign ≠ 0` and the pair identity
  for `K(0), δ, Kd(0), δ'` and the real pair factors. Then the continuation conclusion above
  holds. Proof:
  - `realPairMellinFactor` with this `sign` gives `σ₁` and a measurable rapidly decreasing
    pair `(h, k)` with the formulas of `PairIdentity` for `B = 0`, with `mellin h (-s)` and
    `mellin k (-s)` nonzero for `Re s > σ₁`, and with the factor identity;
  - with `N = σ₀ + 1`: `K(0)` is a.e. strongly measurable, as `K(N) δ^(-N)`; `‖K(0)‖ δ^σ`
    is integrable for `σ ≥ N` by `norm_kernel`; `Z(s) = ∫ K(0) δ^s` for `Re s ≥ N`; likewise
    for `Kd`;
  - `theta_eq_of_pairIdentity` gives the theta identity for `(h, k)`;
  - `exists_continuation` (module `ArchimedeanMellinPair`) gives the conclusion, with
    `L = D⁻¹`, `Ld = Dd⁻¹`, `E = ε`.

### The real Rankin–Selberg kernels

- `quotientDetAbs`, `detAbs_pos`, `quotientDetAbs_pos`: `|det g|` at the representative is
  positive.
- `continuous_quotientDetAbs`, `measurable_quotientDetAbs`: `g ↦ |det g|` is continuous and
  invariant under left multiplication by `N`, since unipotent matrices have determinant `1`.
  Its descent to the quotient is continuous (`RealEqualConvergence.continuous_descend_real`)
  and agrees with `quotientDetAbs` (`RealEqualConvergence.out_eq_descend`).
- `detPower_eq_cpow`: `ArchimedeanLocal.detPower realNormalizedAbs g s = (|det g| : ℂ)^s`.
- `sigmaCompactSpace_quotient`: `N_(r+1)(ℝ) \ GL_(r+1)(ℝ)` is σ-compact. By
  `RealIwasawa.alphaQ_preimage` applied to the whole space, the quotient is the image of
  `ℝ^(r+1) × O(r+1)` under the continuous map `(y, k) ↦ [torus(y) k]`.
- `sigmaFinite_measure`: `D.measure` is σ-finite. It is regular (field `regular` of the
  compatibility structure), hence finite on compact sets, and the quotient is σ-compact.
- `sigmaFinite_haar`, `sigmaFinite_rect`, `sFinite_dualMeasure`: an additive Haar measure on
  `ℝ` is a multiple of Lebesgue measure, so the rectangular measure and
  `realUnequalDualMeasure a D` are s-finite.
- `realEqualIntegrand_eq_mul`, `realUnequalIntegrand_eq_mul`, `realUnequalDualKernel_eq_mul`:
  each kernel at `s` is its value at `0` times `(|det g| : ℂ)^s`. In unequal rank this uses
  `x^(s - (n-m)/2) = x^(-(n-m)/2) x^s` (`Complex.cpow_add`).
- `UnequalPairIdentity`, `EqualPairIdentity`: the definitions above.

In the namespace `Langlands.Global.RankinSelbergGlobal`:
- `RealPairIdentityContinuationStatement`: the proposition above;
- `realPairIdentityContinuation`: its proof. Both parts apply
  `exists_continuation_of_kernels` with the kernels, `δ = quotientDetAbs` and, in unequal rank,
  `δ'(q, x) = quotientDetAbs q`. In unequal rank the dual integral `realUnequalDualIntegral` is
  an iterated integral (rectangular variable first). For `Re s > σ₀` it equals the integral over
  the product measure, by Fubini (`integral_prod`) and hypothesis 3.

## Relation to the literature

Jacquet, *Archimedean Rankin–Selberg integrals* (2009):
- §4.2, pp. 22–23: a `(σ, ψ)` pair is a pair `h, k ∈ S(F^×)`, depending only on `|t|_F`, with
  `∫ h(t) |t|^(-s) d^×t = ε(s, σ, ψ) e^(P(s)) / L(s, σ)` and
  `∫ k(t) |t|^(-s) d^×t = e^(P(1-s)) / L(s, σ̃)`, where `P(s) = A s² + B s + C` with `A > 0`,
  `B ∈ ℝ`, `C ∈ ℂ`. If `(h, k)` is a pair, then so is `(x ↦ h(a x), x ↦ |a| k(a⁻¹ x))` (p. 23).
- Proposition 4.1, pp. 23–25: if `∫ f h d^×x = ∫ f' k d^×x` for every `(σ, ψ)` pair, the
  Mellin transforms of `f` and `f'` continue and satisfy the functional equation. The proof
  derives (4.1), `θ(a) = |a| ∫ f'(x) k(a⁻¹ x) d^×x`, from the scaled pairs.
- §8.1, pp. 53–54: for principal series, Jacquet defines
  `Ψ(θ, W, W', Φ) = ∫ W(g) W'(g) θ(det g) Φ(ε_n g) dg` and
  `Ψ(κ, W̃, W̃', Φ̂) = ∫ W̃(g) W̃'(g) κ(det g) Φ̂(ε_n g) dg`. He states that the assertions of
  Theorem 2.1 for the pair `(n, n)` are equivalent to the identity of these two integrals,
  with a sign, for the pairs `(θ, κ)`. The case `(n, n - 1)` is similar, with
  `Ψ(θ, W, W') = ∫ W(diag(g, 1)) W'(g) θ(det g) |det g|^(-1/2) dg` (p. 54). This section is
  the source of the pair-identity method, which Jacquet writes out only for the equal pair
  `(n, n)` and the adjacent pair `(n, n - 1)`.
- (2.4), (2.5) and Theorem 2.1, p. 6. For `n > n'`, (2.5) defines
  `Ψ_j(s, W, W')`, an integral over `g ∈ N_(n') \ GL_(n')` and over the rectangular block `X`
  placed below `g` in the displayed matrix (Jacquet calls this space `M(m × j, F)`). Here
  `Ψ_0` is the integral (2.4).
  Theorem 2.1(iii) gives, for `n > n' + 1`,
  `Ψ_j(1 - s, ρ(w_(n,n')) W̃, W̃') = ω_π(-1)^(n') ω_π'(-1) γ(s) Ψ_(n-n'-1-j)(s, W, W')`.
  For `n = n' + 1` it gives the same equation with `j = 0`, the same sign (since
  `n - 1 = n'`) and no `ρ(w_(n,n'))`, which is then the identity.
  The Library's unequal dual integral is the left side for `j = n - n' - 1`, so its partner
  on the right is `Ψ_0 = Ψ`. Theorem 2.1(iii) for `n = n'` is
  `Ψ(1 - s, W̃, W̃', Φ̂) = ω_π(-1)^(n-1) γ(s) Ψ(s, W, W', Φ)`.

**How the Lean statement relates to Jacquet.**
- *Direction.* Lean proves one direction of Jacquet's equivalence on p. 53: the pair identity
  (together with convergence) implies the continuation and the functional equation. It is
  the deduction in the proof of Proposition 4.1, applied to the Rankin–Selberg integrals over
  `X = N_m \ GL_m(ℝ)` (and `X × M_((n-m-1) × m)(ℝ)` for the unequal-rank dual integral) with
  `δ = |det|`, as Jacquet does on p. 54. Lean does not prove the pair identity for any
  Rankin–Selberg integral.
- *Unequal ranks.* For `n = m + 1` the rectangular factor is the zero space and
  `UnequalPairIdentity` is the `(n, n - 1)` identity of §8.1. For `n > m + 1` Jacquet does not
  display a pair identity. Lean's `UnequalPairIdentity` applies the same method to the two
  integrals of Theorem 2.1(iii) with `j = n - m - 1`: the larger kernel (2.5) on the dual
  side and (2.4) on the other.
- *Which pairs.* Lean's `PairIdentity` uses only the polynomials `P(s) = s² + B s`
  (`A = 1`, `C = 0`, any real `B`), which is the family closed under Jacquet's scaling that
  contains `P(s) = s²`. Unlike Jacquet, it asks for the identity for every measurable rapidly
  decreasing `(h, k)` on `(0, ∞)` with the prescribed Mellin transforms, not only for pairs in
  `S(F^×)`. The functions `h, k` are evaluated at `|det g|`, which matches Jacquet's radial
  `θ(det g)`.
- *Normalizations.* Lean's Mellin transform is Mathlib's on `(0, ∞)`. For a radial function on
  `ℝ^×`, Jacquet's integral over `F^×` is a positive constant multiple of it, the constant
  depending on the normalization of `d^×t`. In Lean the factor `sign` is placed in the Mellin
  transform of `h`. So for a Jacquet pair `(θ, κ)`, Lean's identity corresponds to Jacquet's
  identity `Ψ(θ, …) = sign⁻¹ Ψ(κ, …)` with matching normalizations. The `L`- and `ε`-factors
  are the Library's `realPairLFactor` and `realPairEpsilon` used in `UnequalEquation` and
  `EqualEquation`. The block lists `dds`, `ees` are arbitrary: no contragredient
  identification is needed or claimed.
- *Sign.* Here `sign` is an arbitrary nonzero parameter, and the conclusion has the same
  `sign`. Module `RealUniformPairIdentityReduction` takes it from Theorem 2.1(iii), p. 6:
  `ω_π(-1)^(n-1)` in equal rank `n`, and `ω_π(-1)^m ω_π'(-1)` for ranks `n > m`. In equal rank
  this is also the sign `∏_i μ_i(-1)^(n-1)` that the computation of §8.2 (p. 56) produces.
  The lower display on p. 53 (the equal-rank pair identity) instead has the factor
  `∏_i μ_i(-1)^(-n-1) ∏_j ν_j(-1)`. Its extra factor `∏_j ν_j(-1) = ω_π'(-1)` can equal
  `-1`, so the Lean sign is not taken from that display.
- *Convergence.* Absolute convergence on a right half-plane is a hypothesis here. For the
  uniform Whittaker models it is proved in the Library (`realEqualPairConvergence` and
  `realUnequalPairConvergence`); module `RealUniformPairIdentityReduction` combines these with
  the present statement.
- *Conclusion.* As in `ArchimedeanMellinPair`: meromorphic continuation and the multiplied-out
  functional equation off a discrete closed set. The holomorphic-multiple and vertical-strip
  assertions of Theorem 2.1(ii) are not stated.

**Not proved here.**
- The pair identity for the real Rankin–Selberg integrals (Jacquet §§8–11).
- That the pair identity for Lean's class of `(h, k)` follows from Jacquet's identity for pairs
  in `S(F^×)` (this would use injectivity of the Mellin transform and absolute continuity of the
  push-forward of the measures under `|det|`).
