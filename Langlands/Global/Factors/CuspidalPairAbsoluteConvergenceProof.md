# Jacquet–Shalika I, Theorem (5.3), from Lemma (5.2)

Lean module: `Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof`.
It proves `CuspidalPairAbsoluteConvergenceReductionStatement`. It imports the
statement module
`Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceStatement`, the two
helper modules ported with this file (`Langlands.Analysis.LandauDirichlet`,
`Langlands.Representation.Unramified.UnitarySpectrumConjugation`), and published
Library modules named below.

## Main theorem

```lean
theorem Langlands.Global.cuspidalPairAbsoluteConvergenceReduction :
    CuspidalPairAbsoluteConvergenceReductionStatement.{u, uQ}
```

This is exactly the published statement, with both universes. It is
`CuspidalSelfPairContinuationStatement.{u, uQ} →
CuspidalPairAbsoluteConvergenceStatement.{u, uQ}`: Lemma (5.2) implies Theorem
(5.3). The implication is proved as
`Langlands.Global.cuspidalPairAbsoluteConvergence_of_selfPairContinuation`.

Recall the data of Theorem (5.3): a number field `F` with compact adele
quotient; actual cuspidal realizations `T` of `GL_(r+1)` and `T'` of `GL_(t+1)`
with unitary central characters; presentations `P`, `P'`; a finite set `S` of
finite places containing both exceptional sets; and `s` with `Re s > 1`. The
three conclusions are as follows.

1. The double series of `‖logEulerTerm P P' hP hP' v n s‖`, over
   `{v ∉ S} × ℕ`, converges.
2. `∑_(v ∉ S) ‖partialEulerFactor P P' hP hP' v s - 1‖` converges.
3. The Euler product has the value `exp` of the sum of the double series
   (`HasProd`).

## Declarations

All are in the namespace `Langlands.Global.CuspidalPairAbsoluteConvergence`,
except the two main theorems.

### Local logarithms

- `hasSum_pow_succ_div`: `∑_(k≥0) w^(k+1)/(k+1) = -log(1 - w)` for `‖w‖ < 1`
  (Mathlib's `Complex.hasSum_taylorSeries_neg_log`, shifted by one).
- `multiset_hasSum_log`, `multiset_exp_log`: the same for a finite multiset of
  `w`. The exponential of the sum of the logarithms is `(∏ (1 - w))⁻¹`.
- `sum_map_pow_product`: `∑_((α, β)) (α β x)^k = tr(a^k) tr(b^k) x^k` over the
  product multiset.
- `exists_hasSum_pairLog` (JS I, (5.3.1)): if every `‖α β x‖ < 1`, then
  `((pairEulerPolynomial a b).eval x)⁻¹ = exp w`, where `w` is the sum of
  `∑_(k≥0) tr(a^(k+1)) tr(b^(k+1)) x^(k+1)/(k+1)`. The value of the pair Euler
  polynomial is the published `CuspidalPairEulerConvergence.eval_pairEulerPolynomial`.

### Local inputs for unitary cuspidal presentations

- `norm_eigenvalue_le_sqrt` (JS I, Corollary (2.5), non-strict form): for `T`
  with unitary central character and a presentation `Q`, every Satake parameter
  outside `Q.exceptional` has norm `≤ q_v^(1/2)`. Proof: the local component is
  irreducible, admissible and unitarizable (`cuspidalUnitaryLocalUnitarity`).
  Its spherical spectrum is realized by an unramified principal series of which
  it is a spherical subquotient
  (`Unramified.hasSphericalSpectrum_of_hasSphericalHeckeSpectrum`). It is
  generic for the standard local additive character
  (`cuspidalUnitaryLocalGenericity`,
  `HeckeFunctionalEquation.standardFiniteAdditiveComponent`). So it is an
  unramified generic constituent, and the published
  `RankinSelberg.UnramifiedUnitary.norm_unramifiedClass_le_sqrt` applies.
- `eigenvalues_eq_conjSpectrum`: for a contragredient realization `Td` and a
  presentation `Qd`, outside both exceptional sets, the spectrum of `Qd` is the
  complex conjugate of that of `Q`. The published
  `CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf`
  gives `A⁻¹`. `conjSpectrum_eq_map_inv_of_hasSphericalHeckeSpectrum` (helper
  module) gives `conj A = A⁻¹`.

### Norms and summability

- `logExponent x = (n + 1) log q_v` and
  `selfCoeff P hP x = ‖tr(A_v^(n+1))‖² / (n + 1)`, for `x = (v, n)`.
  `selfCoeff` is nonnegative, and `log 2 ≤ logExponent x`.
- `exp_neg_logExponent`, `spectralPoint_pow_eq_exp`,
  `norm_spectralPoint_pow`: `q_v^(-(n+1)s) = exp(-(n+1) log q_v · s)`, and its
  norm.
- `norm_powerTrace_le`: `‖tr(a^k)‖ ≤ n B^k` when all parameters have norm
  `≤ B`.
- `norm_logEulerTerm`: `‖logEulerTerm‖ = ‖tr A^(n+1)‖ ‖tr A'^(n+1)‖/(n+1) ·
  exp(-(n+1) log q_v · Re s)`.
- `norm_logEulerTerm_le`, `selfCoeff_mul_exp_le`: given the bounds `q_v^(1/2)`,
  the terms are at most a constant times `(q_v^(1 - σ))^(n+1)`.
- `summable_of_le_geometric`: a family dominated by `C (q_v^(1-σ))^(n+1)` with
  `σ > 2` is summable. The fibers are geometric, and
  `∑_v q_v^(-(σ-1)) < ∞` (published `HeckeEulerProduct.summable_absNorm_rpow`).
- `summable_of_summable_except`: a nonnegative family on `V × ℕ` is summable if
  its fibers are, and if it is summable on the `v` outside a finite set.

### The product

- `exists_hasSum_logEulerTerm`: for `Re s > 1` and `v ∉ S`, the local factor is
  `exp` of the sum over `n` of the terms. The bounds `q_v^(1/2)` give
  `‖α β q_v^(-s)‖ ≤ q_v^(1 - Re s) < 1`.
- `summable_and_hasProd_of_summable` (JS I, (5.3.2)): for `Re s > 1`, if the
  double series converges absolutely, then conclusions 2 and 3 hold. The sum of
  the double series is the sum over `v` of the inner sums
  (`HasSum.prod_fiberwise`). Exponentiating gives the product (`HasSum.cexp`).
  For conclusion 2, `‖exp w_v - 1‖ ≤ 2 ‖w_v‖` once `‖w_v‖ ≤ 1`
  (`Complex.norm_exp_sub_one_le`). Here `‖w_v‖` is at most the summable inner
  sum of norms.

### The self-pair and Landau's theorem

- `exceptEquiv S E`: the places outside `S` and outside `E`, as the places
  outside `S ∪ E`.
- `logEulerTerm_self_eq`: for the contragredient presentation, the self-pair
  term is the general Dirichlet term with coefficient `selfCoeff` and exponent
  `logExponent`. This uses `tr(Ã^k) = conj(tr A^k)` and `z · conj z = ‖z‖²`.
- `norm_conjSpectrum_le`: conjugation keeps the bounds.
- `summableAt_selfCoeff` (JS I, (5.3.3) and Landau's theorem). Given Lemma
  (5.2), for every `σ > 1`, the series
  `∑_((v,n)) ‖tr A_v^(n+1)‖²/(n+1) · q_v^(-(n+1)σ)` over `v ∉ S` converges.

### Theorem (5.3)

- `half_bound`: `a b/d · e ≤ ½ (a²/d · e + b²/d · e)`.
- `cuspidalPairAbsoluteConvergence_of_selfPairContinuation`.

## Proof of the main theorem

Fix the data above, with `σ = Re s > 1`.

1. **The self-pair.** Choose a contragredient `Td` of `T`
   (`cuspidalContragredientExistence`) and a presentation `Pd` of `Td` in the
   universe `uQ` (`cuspidalDualPresentationExistence`). The exceptional set of
   `Pd` need not lie in `S`. So Lemma (5.2) is applied with
   `S' = S ∪ Pd.exceptional`. It gives a function `L` holomorphic on
   `Re s > 1`, equal to the Euler product over `v ∉ S'` on some right
   half-plane `Re s > σ*`. On `Re s > max(σ*, 2) + 1`:
   - the double series for `(P, Pd)` over `v ∉ S'` converges absolutely, by the
     geometric bounds. The parameters of `Pd` are conjugates of those of `P`, so
     they also have norm `≤ q_v^(1/2)`;
   - so the Euler product is `exp` of the double series
     (`summable_and_hasProd_of_summable`). By uniqueness of limits, `L` is `exp`
     of the general Dirichlet series with coefficients `selfCoeff` and
     exponents `logExponent`, indexed by `{v ∉ S, v ∉ Pd.exceptional} × ℕ`
     (`logEulerTerm_self_eq`, reindexed by `exceptEquiv`);
   - that series converges at the real point `max(σ*, 2) + 1`.

   The coefficients are nonnegative and the exponents are `≥ log 2 > 0`. So
   `GeneralDirichlet.summableAt_of_exp` (helper module, Landau's theorem) gives
   convergence at every real `σ > 1`. The finitely many places of
   `Pd.exceptional \ S` are added back by `summable_of_summable_except`. At each
   of them the series over `n` is dominated by the geometric series of ratio
   `q_v^(1-σ) < 1`, by the bound `q_v^(1/2)` for `P`.
2. **The general pair: conclusion 1** (JS I, (5.3.5)). By Cauchy–Schwarz,
   `‖tr A^k‖ ‖tr A'^k‖ ≤ ½(‖tr A^k‖² + ‖tr A'^k‖²)`, so `‖logEulerTerm‖` is at
   most half the sum of the self-pair terms of `P` and `P'` at `σ`
   (`norm_logEulerTerm`, `half_bound`). Both are summable by step 1, applied to
   `T` and to `T'`.
3. **Conclusions 2 and 3.** `summable_and_hasProd_of_summable` applied to
   `(P, P')`.

## Sources and provenance

- H. Jacquet and J. A. Shalika, *On Euler products and the classification of
  automorphic representations I*, Amer. J. Math. 103 (1981), 499–558,
  registered as
  `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`
  (SHA256 `c6b669ccf00a3ce35c10aa60f3dc7538d6269bf279791e5286b893c597275620`;
  printed page = PDF page + 498).
  - Corollary (2.5), p.515 (PDF 17): the eigenvalues of the class of a unitary,
    generic, unramified representation are in absolute value `< q^(1/2)`.
    Remark (2.6)(3): this applies to local components of cusp forms.
  - (5.1), p.554 (PDF 56); Lemma (5.2), pp.554–555 (PDF 56–57); Theorem (5.3),
    p.555 (PDF 57).
  - Proof of Theorem (5.3), pp.555–557 (PDF 57–59): the local logarithm (5.3.1),
    the global exponential (5.3.2), the nonnegative series (5.3.3) for
    `π' = π̃`, the singularity argument with Lemma (5.2) (p.556), Cauchy–Schwarz
    for (5.3.5), and commutative hence absolute convergence of the product
    (p.557).
- G. H. Hardy and M. Riesz (1915), Theorem 10, p.10 (PDF 26), registered as
  `hardy-riesz-1915-dirichlet-series`, for Landau's theorem (see
  `Langlands/Analysis/LandauDirichlet.md`).

The proof follows Jacquet–Shalika's route.
It differs in three points.

- **Local bounds.** Corollary (2.5) is used in the non-strict form
  `|α| ≤ q^(1/2)`. That is what the published `norm_unramifiedClass_le_sqrt`
  gives for all ranks, and it suffices. The local logarithm is used only for
  `Re s > 1`, where `|α β q^(-s)| ≤ q^(1 - Re s) < 1`. The alternative, the
  weak bound `CuspidalSatakeBound.norm_le_of_hasUnitaryCentralCharacter`,
  is not used.
- **The finite set.** Lemma (5.2), as published, needs a finite set containing
  the exceptional set of the dual presentation. The published
  `cuspidalDualPresentationExistence` gives no control of the exceptional set
  of `Pd`, and this proof constructs no other presentation. So Lemma (5.2) is
  applied with `S ∪ Pd.exceptional`, and the finitely many extra places are
  handled with the local bound. Jacquet–Shalika take one set `S` for all
  representations involved.
- **Landau.** Jacquet–Shalika take `log L_S` near the real point of the line of
  convergence. The helper module uses `-L'/L` instead (see its Markdown).

## What is not asserted

- `CuspidalPairAbsoluteConvergenceStatement` itself: it follows from the
  reduction and `CuspidalSelfPairContinuationStatement` (Lemma (5.2)), proved as
  `cuspidalSelfPairContinuation` (module
  `Langlands.Global.Factors.CuspidalSelfPairContinuationProof`); the Library
  does this in `Langlands.Global.cuspidalPairAbsoluteConvergence` (module
  `Langlands.Global.Factors.CuspidalPairAbsoluteConvergence`). This module does
  not prove Lemma (5.2).
- The strict bound `|α| < q^(1/2)`, or any statement at the archimedean places.

## Lean checks

In the Lean environment in which it was written, `lake build` compiles the
module with no errors or warnings. The main theorem depends
only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
