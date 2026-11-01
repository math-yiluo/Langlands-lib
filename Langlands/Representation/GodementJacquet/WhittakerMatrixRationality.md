# Rationality of full-matrix Whittaker integrals

Module `Langlands.Representation.GodementJacquet.WhittakerMatrixRationality`,
namespace `Langlands.GodementJacquet.WhittakerTorus` (generic lemmas) and
`Langlands.GodementJacquet.WhittakerTorus.Padic`.

Notation and instances are those of `WhittakerIwasawaReduction`: `F` is a
p-adic field with its canonical topological data, `G = GL_(n+1)(F)`,
`K = GL_(n+1)(O)`, `dg` is `generalLinearHaar`, `da` is the product of the
normalized multiplicative Haar measures on `A = (Fˣ)^(n+1)`, `|·|` is the
normalized absolute value, `q` the residue cardinality, and `δ` the upper-Borel
modulus. Write `Z(Φ, s, W) = ∫_G Φ(g) W(g) |det g|^s dg`
(`GodementJacquet.Padic.matrixIntegral`).

Main theorem (`IsWhittakerLike.hasRationalContinuation`). Assume
`FiniteFunctionMellinStatement`. Let `W` satisfy `IsWhittakerLike F ψ W`, let
`Φ` be a Schwartz–Bruhat function on all square matrices, and let `t ∈ ℂ`.
Suppose that `Φ(g) W(g) |det g|^s` is integrable for `dg` whenever `Re s` is
larger than some real `c`. Then `s ↦ Z(Φ, s + t, W)` has a rational
continuation in `q^(-s)` (`HasRationalContinuation`): there are a rational
function `R` and a real `a` with `Z(Φ, s + t, W) = R(q^(-s))` (and the
denominator of `R` nonzero at `q^(-s)`) for `Re s > a`.

## Source and provenance

The content is internal and derived. It is the rationality half of a proof
that full-matrix Whittaker integrals converge and are rational. Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
convolutions*, Amer. J. Math. 105 (1983), Section (5.2), printed pages
420–421, assert this for a representation `σ` of Whittaker type acting on its
Whittaker model: the full-matrix integrals "converge for Re(s) large, define
rational functions of X = q^(-s)". That section completes results of the same
authors' *Automorphic forms on GL(3) I*, Ann. of Math. 109 (1979). There,
printed page 186 (proof of Proposition (3.1), for irreducible generic
representations), convergence comes from majorizing `W` by a gauge and
rationality from the identity (3.1.4) with matrix coefficients. The route
formalized here is different: it adapts the proof of Theorem (2.7) of the
1983 paper, printed pages 391–392, from the Rankin–Selberg integrals to the
full-matrix integrals. That proof uses the Iwasawa decomposition, the
coordinates (4), the torus expansion of Whittaker functions, and the Mellin
integrals (5)–(6).
Here the integral is reduced through `G = N A K` and the torus
expansion of `W` to finitely many Mellin integrals of finite functions. The
final step is the proposition `FiniteFunctionMellinStatement`, taken from JPSS
(1983), printed page 392, displays (5)–(6). The convergence hypothesis is the
other half of the argument (module `WhittakerMatrixConvergence`).

## Declarations

Generic:

- `exists_common_halfPlane S P h`: if for each `i` in a finite set `S` the
  condition `P i s` holds for `Re s > c_i`, then all of them hold for `Re s`
  beyond a single bound. Proof by induction on `S`, taking maxima.
- `exists_continuation_sum S f h`: a finite sum of functions with rational
  continuations has a rational continuation (`continuation_sum` after choosing
  the rational functions).

p-adic:

- `normalizedAbs_units_pos`, `normalizedAbs_prod_pos`, `normalizedAbs_prod_mul`,
  `continuous_normalizedAbs_prod`: `|∏ a_i|` is positive, multiplicative and
  continuous on `A`.
- `borelModulus_pos`, `borelModulus_mul`, `continuous_borelModulus`: the same
  for `δ`. Multiplicativity uses `(b a)_i / (b a)_j = (b_i / b_j)(a_i / a_j)`.
- `twistedCharacter F χ t`: the function `a ↦ χ(a) δ(a)⁻¹ |∏ a_i|^t`.
- `isFiniteFunction_twistedCharacter`: if `χ` is a finite function, so is
  `twistedCharacter F χ t`. The factors `δ⁻¹` and `|∏ a_i|^t` are continuous
  characters (`IsFiniteFunction.of_mul_apply`; the second uses
  `Complex.mul_cpow_ofReal_nonneg` and continuity of `cpow` on the slit
  plane), and products of finite functions are finite
  (`IsFiniteFunction.mul`).
- `sliceTest F ψ Φ k`: the slice integral `x ↦ ∫_N Φ(u diag(x) k) ψ_N(u) du`
  as a Schwartz–Bruhat function on `F^(n+1)`
  (`sliceIntegral_rightTranslate_mem`); `sliceTest_apply` unfolds it.
- `IsWhittakerLike.hasRationalContinuation`: the main theorem.

## Proof of the main theorem

1. `IsWhittakerLike.exists_cosetSum` gives an open subgroup `K₀ ≤ K` and a
   finite set `S ⊆ K`. The integrand is right `K₀`-invariant, and integrals
   over `K` of right `K₀`-invariant functions are sums over `S` weighted by
   `vol(K₀)`. The field `expansion` gives, for each `k`, a finite set `X_k` of
   finite functions and coefficients `φ_(k,χ)` with
   `W(diag(a) k) = Σ_{χ ∈ X_k} φ_(k,χ)(ratios a) χ(a)`.
2. For each `k` and `χ ∈ X_k`, `torusMellin` (module `WhittakerTorusMellin`)
   applies to `η = twistedCharacter F χ t`, `φ = φ_(k,χ)` and
   `J = sliceTest F ψ Φ k`. The torus integral `M_(k,χ)(s)` of
   `torusIntegrand F φ J η s` is integrable for `Re s` large and has a
   rational continuation. `exists_common_halfPlane` gives a common bound `c₁`
   for the finitely many integrability conditions.
3. For `Re s > max(c - Re t, c₁)` the integrand at `s + t` is integrable, and
   `integral_iwasawa`, the coset sum, `integral_unipotent_matrixIntegrand` and
   the expansion give
   `Z(Φ, s + t, W) = Σ_{k ∈ S} vol(K₀) Σ_{χ ∈ X_k} M_(k,χ)(s)`. The `K₀`-invariance
   needed for the coset sum comes from the right invariance of the integrand
   at `u diag(a) (k k₀) = (u diag(a) k) k₀`. The pointwise identity
   `δ(a)⁻¹ · W(diag(a) k) |∏ a_i|^(s+t) J(a) = Σ_χ torusIntegrand F φ_(k,χ) J η_χ s a`
   uses `|∏ a_i|^(s+t) = |∏ a_i|^s |∏ a_i|^t`. The exchange of the sum over
   `χ` with the `A`-integral uses `integral_finsetSum` and step 2.
4. The right-hand side has a rational continuation (`exists_continuation_sum`
   twice and `hasRationalContinuation_const_mul`). It agrees with
   `Z(Φ, s + t, W)` on a right half-plane, so `continuation_of_eq_on_right`
   transfers the continuation.

## Hypotheses

The main theorem keeps `FiniteFunctionMellinStatement` as an explicit
hypothesis and takes convergence on a right half-plane as a hypothesis.
The Library proves `FiniteFunctionMellinStatement` as
`Langlands.RankinSelberg.finiteFunctionMellin` (module
`Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof`), so
downstream users can supply the hypothesis.
