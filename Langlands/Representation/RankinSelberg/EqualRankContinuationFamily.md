# Linearity, right translation and the trilinear continuation family

Authors: Worker 233 and Worker 762. Written for helper task
`bd2991bb-7582-4786-bb5b-da489d7eb049`; its consumer is the proof task
`1f6f86ac-1105-4f57-b067-1fe692fb2683` for the published statement
`Langlands.RankinSelberg.EqualRankContinuedFormsStatement`.

This module proves the multilinearity and the right-translation law of the
actual equal-rank Rankin--Selberg integrals of the Library, and packages their
rational continuations, under the published `EqualRankAnalyticConclusion`, as a
trilinear map with a monomial translation law. It works over a general field
`F` with a topology, an arbitrary measurable structure and measure `μ` on the
quotient `LeftUnipotentQuotient n F = N \ GL_(n+1)(F)`, and representations in
independent universes. `[IsTopologicalRing F]` is added only where the
right-translation homeomorphism `rightTranslate` or the dual-model maps of the
Library require it: `QuotientIntegration.rightTranslate` is defined for a
topological group, and Mathlib makes `GL_(n+1)(F)` (the units of the matrix
ring) a topological group from `IsTopologicalRing F`; the published
`DualModels` section assumes `IsTopologicalRing F` as well. The linearity
results, the determinant identities and the definition of the family use only
`[Field F] [TopologicalSpace F]`. Nothing published is redefined: the module uses
`equalRankIntegrand`, `equalRankIntegral`, `EqualRankConverges`,
`equalRankModelIntegral`, `HasRationalContinuation`,
`EqualRankAnalyticConclusion`, `determinantWeight`, `lastRow`, `spectralPoint`,
`modelRepresentation`, `firstDualModelMap` and `secondDualModelMap` as
published.

Throughout, `W, W₁, W₂` are Whittaker functions, `W', W'₁, W'₂` inverse
Whittaker functions, `Φ, Φ₁, Φ₂` Schwartz--Bruhat functions on rows
`Fin (n + 1) → F`, `c` and `s` complex numbers. The integrand at the class of
`g` is `W(g) W'(g) Φ(lastRow g) |det g|^s` (`equalRankIntegrand_mk`).

## Linearity of the integrand and of the integral

- `equalRankIntegrand_add_left`, `equalRankIntegrand_add_middle`,
  `equalRankIntegrand_add_right`: at every point of the quotient, the integrand
  of a sum in one argument is the sum of the integrands.
- `equalRankIntegrand_smul_middle`, `equalRankIntegrand_smul_right`: the
  integrand of `c • W'` (resp. `c • Φ`) is `c` times the integrand (the first
  argument is covered by the published `equalRankIntegrand_smul_left`).
- `equalRankIntegral_add_left`, `equalRankIntegral_add_middle`,
  `equalRankIntegral_add_right`: if both summands converge absolutely at `s`
  (`EqualRankConverges`), the integral of the sum is the sum of the integrals.
  Only the convergence of the two summands is assumed; the sum then converges
  as well, and Mathlib's `integral_add` applies.
- `equalRankIntegral_smul_middle`, `equalRankIntegral_smul_right`: the integral
  is homogeneous for every `s`, without any convergence hypothesis, because
  the Bochner integral commutes with constant multiplication
  (`integral_const_mul`).

## Right translation

- The imported `lastRow_mul_eq_vecMul (h g)` states
  `lastRow (h * g) = vecMul (lastRow h) g`: the last row of a product is the
  last row of `h` times the matrix `g`. It holds by definition of matrix
  multiplication and is shared through [`QuotientIntegrals`](QuotientIntegrals.md).
- `determinantWeight_neg_mul_self`: `|det g|^(-s) · |det g|^s = 1`.
- `equalRankIntegrand_translate`: let `Wg`, `W'g`, `Φg` satisfy
  `Wg(h) = W(h g)`, `W'g(h) = W'(h g)` and `Φg(x) = Φ(x g)`. Then at every point
  `x` of the quotient the integrand of `(Wg, W'g, Φg)` equals
  `|det g|^(-s)` times the integrand of `(W, W', Φ)` at the right translate
  `x g`. At the class of `h`, the value is
  `W(hg) W'(hg) Φ(lastRow h · g) |det h|^s`; by `lastRow_mul_eq_vecMul` the Schwartz
  argument is `lastRow (h g)`, and by multiplicativity of the determinant weight
  (`determinantWeight_mul`) `|det h|^s = |det g|^(-s) |det (h g)|^s`.
- `equalRankIntegral_translate`: assume a Borel structure on the quotient and
  `hμ : ∀ g, MeasurePreserving (rightTranslate _ g) μ μ`, which is exactly the
  right-invariance field `IsCompatible.right_invariant` of the Library's
  quotient measures. Then for every complex `s`

  `equalRankIntegral ψ abv μ Wg W'g Φg s = |det g|^(-s) · equalRankIntegral ψ abv μ W W' Φ s`

  (with `|det g|^(-s)` written `determinantWeight abv g (-s)`). The proof
  rewrites the integrand by `equalRankIntegrand_translate`, pulls out the
  constant, and changes variables along the measure-preserving homeomorphism
  `rightTranslate _ g` (`MeasurePreserving.integral_comp` with its measurable
  embedding). That change of variables holds for the total Bochner integral
  without any integrability hypothesis, so the identity holds at every `s`,
  also where neither side converges (then both sides are zero), whereas JPSS
  state it away from poles of the continued integrals.
- `equalRankConverges_translate_iff`: under the same hypotheses, `(Wg, W'g, Φg)`
  converges absolutely at `s` if and only if `(W, W', Φ)` does. Multiplication
  by the nonzero constant `|det g|^(-s)` and composition with a
  measure-preserving embedding both preserve integrability.

These are the translation and linearity properties of the integrals
`Ψ(s, W, W', Φ)` that Jacquet, Piatetski-Shapiro and Shalika use in §2.10 of
*Rankin--Selberg Convolutions* (1983) to show that the continued forms are
invariant up to `|det g|^(-s)`; here they are proved for the Library's
quotient integrals.

## The spectral form of the determinant factor

`determinantWeight_neg_eq_spectralPoint_zpow (hq : 0 < q) abv g m (hg : abv (det g) = q ^ m) s`
states `|det g|^(-s) = spectralPoint q s ^ m`, where
`spectralPoint q s = q^(-s)`. The absolute value `abv` is an explicit argument
and `g` may lie in `GL_d(F)` for any `d`, matching the published
`determinantWeight_eq_spectralPoint_zpow`; the task's case is `d = n + 1`. It is the published
`determinantWeight_eq_spectralPoint_zpow` at exponent `-m` and parameter `-s`,
together with `spectralPoint q (-s) = (spectralPoint q s)⁻¹`.

## The trilinear continuation family

Let `π`, `σ` be complex representations of `GL_(n+1)(F)` on `V`, `W`,
`ℓ : glFunctionals ψ n π`, `ℓ' : glInverseFunctionals ψ n σ`, `hq : 1 < q` and
`hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ'`. The first component of
`hA` gives, for each triple, a real `a` such that the model integral converges
absolutely for `a < Re s`; the second gives a rational continuation.

`equalRankContinuationFamily hq hA : coefficientModel π ℓ →ₗ[ℂ]
coefficientModel σ ℓ' →ₗ[ℂ] SchwartzBruhat (Fin (n + 1) → F) →ₗ[ℂ]
RationalFunctions` sends `(f, f', Φ)` to the continuation chosen by `hA`
(private `continuationValue`). The data `q ψ abv μ π σ ℓ ℓ'` are implicit; they
are determined by `hA`.

- `equalRankContinuationFamily_spec`: the value is a rational continuation of
  `equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ`.
- `equalRankContinuationFamily_eq`: any rational continuation `R` of that model
  integral equals the value, by `HasRationalContinuation.unique` (this uses
  `1 < q`).

Linearity is proved by this uniqueness and never by evaluating rational
functions at points. For additivity in, say, the first argument, `hA` gives
half-planes `a₁ < Re s` and `a₂ < Re s` of convergence for `(f₁, f', Φ)` and
`(f₂, f', Φ)`. On the common half-plane `max a₁ a₂ < Re s` both summands
converge, so the integral of `(f₁ + f₂, f', Φ)` is the sum of the two integrals
(`equalRankIntegral_add_left`). The sum of the two chosen continuations is a
continuation of the sum of the integrals (`continuation_add`), hence, by
`continuation_of_eq_on_right` on that half-plane, a continuation of the
integral of the sum; uniqueness identifies it with the chosen value. The other
two additivity laws are identical. For scalars, the integral of `c • f` equals
`c` times the integral for every `s`, so `c • R = RatFunc.C c * R` is a
continuation by `hasRationalContinuation_const_mul` and
`continuation_of_eq_on_right` (private `continuation_smul`).

## The monomial translation law

`equalRankContinuationFamily_translate` assumes `[IsTopologicalRing F]`, a
Borel structure on the quotient, `hμ` as above, an integer `m` with
`hg : abv (det g) = q ^ m`, and `Φg` with `Φg(x) = Φ(x g)`. It states

`equalRankContinuationFamily hq hA (modelRepresentation π ℓ g f) (modelRepresentation σ ℓ' g f') Φg = X ^ m * equalRankContinuationFamily hq hA f f' Φ`.

The model representation acts by right translation, `(g · f)(h) = f(h g)`, by
definition, so `equalRankIntegral_translate` and
`determinantWeight_neg_eq_spectralPoint_zpow` give, for every `s`, that the
integral of the translated triple is `spectralPoint q s ^ m` times the
original integral. The published `HasRationalContinuation.monomial_mul` (with
constant `1`) states that `X ^ m * R` continues `spectralPoint q s ^ m` times a
function continued by `R`, and uniqueness concludes.

## Dual-model compatibility

With `[IsTopologicalRing F]`:

- `firstDualModelMap_modelRepresentation`: the first dual model map sends the
  right translate of `f` by `g` to the right translate of its image by the
  inverse transpose `inverseTranspose (n + 1) F g`, in the model of
  `inverseTransposePullback π` with functional `firstDualFunctional ψ π ℓ`.
  The dual function is `x ↦ f(w · x^ι)` with `w` the long Weyl element and
  `x^ι` the inverse transpose; since `ι` is a multiplicative involution,
  `w · (x · g^ι)^ι = w · x^ι · g`, which is the value of the translated
  function.
- `secondDualModelMap_modelRepresentation`: the same for `σ`, `ℓ'`.
- `dualEqualRankModelIntegral_eq`: the published dual integral
  `dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ` is, by definition, the
  equal-rank model integral for the character `ψ.scale (-1)`, the pulled-back
  representations and dual functionals, at the dual model images of `f`, `f'`
  and the same `Φ`.

## Provenance

Derived. Jacquet, Piatetski-Shapiro and Shalika, *Rankin--Selberg
Convolutions*, Amer. J. Math. 105 (1983), §2.10 (printed p.396, PDF p.31;
registered source `jpss-1983-rankin-selberg`) let `π` act by right
translations on its Whittaker model and state, as their equation (2), the
translation identity
`Ψ(s, π(g)W, π'(g)W', ρ(g)Φ) = |det g|^(-s) Ψ(s, W, W', Φ)` with
`(ρ(g)Φ)(x) = Φ(x g)`, read off from the integral
`∫_{N\G} W(g) W'(g) Φ(η g) |det g|^s dg` for `Re(s)` large; their Proposition
then bounds the dimension of the space of trilinear forms `B` satisfying this
law (their (4)), the continued integrals being such forms.
Those are the only facts of the source used here; the integral
`Ψ(s, W, W', Φ)` is defined in §2.1 and Theorem 2.7. The formulation over the
Library's right quotient `N \ GL_(n+1)` with a supplied right-invariant
measure, the spectral variable `X = q^(-s)`, the packaging of the
continuations as a trilinear map, and the dual-model compatibility are
internal to the Library.
