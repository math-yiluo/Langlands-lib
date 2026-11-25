# The weak continuation of intertwining operators from that of Eisenstein series

Module `Langlands.Global.AdelicIntertwiningWeakContinuationReduction`. Its target is the Library's
`Langlands.Global.IntertwiningWeakMeromorphicContinuationStatement` (module
`Langlands.Global.AdelicIntertwiningContinuationReduction`). All declarations are in the
namespace `Langlands.Global`.

The module proves the target from two premises. It proves neither premise.

## Statement: `IntertwiningWeakContinuationReductionStatement`

```
EisensteinMeromorphicContinuationStatement.{u} →
  IntertwiningConstantTermDifferenceStatement.{u} →
    IntertwiningWeakMeromorphicContinuationStatement.{u}
```

- `EisensteinMeromorphicContinuationStatement` (module `AdelicEisensteinContinuationStatement`)
  is BL Theorem 2.3 (1) in the Fréchet form of BL's Corollary in §8.6. The Eisenstein series
  `E(φ, λ)` has a continuation `E'`. Near every point and in every linear coordinate system,
  `E'` is meromorphic with values in a Fréchet space of uniform moderate growth.
- `IntertwiningConstantTermDifferenceStatement` (module `AdelicIntertwiningDifferenceStatement`)
  is the difference-operator input of BL §8.5. It gives a point `t ∈ G(𝔸)`, a polynomial `f`
  and roots `root j(λ)` entire in `λ`, with the following properties on the `R₀`-regular region:
  - `f(T_t)` kills `M(w, λ)φ`;
  - `∏ j (T_t − root j λ)` kills `m_Q^{−wλ} C_Q E(φ, λ) − M(w, λ)φ`;
  - `f(root j λ₀) ≠ 0` for all `j` at one point `λ₀`.

  Here `T_t` is left translation by `t`. That module's Markdown gives the exact form and its
  correspondence with BL.

The theorem `intertwiningWeakMeromorphicContinuation_of_difference` proves the implication.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`:

- §8.5, pp. 224–225 (PDF pp. 38–39; TeX `1911.02342.tex` lines 3417–3486). BL form the
  resultant `R(λ)` of `f` and `g(λ, ·)`, an analytic function of `λ` that is not identically
  `0`. They write `u(x, λ) f(x) + v(x, λ) g(x, λ) = R(λ)`, where `u` and `v` are polynomials in
  `x` with coefficients analytic in `λ`. On `𝒜_Q(wμ_P)` one has `f(T_a) = 0`, and the
  restriction `D̃(λ)` of `D(λ)` is `g(λ, T_a)`. Evaluating the identity at `T_a` on that space
  gives `v(T_a, λ) D̃(λ) = D̃(λ) v(T_a, λ) = R(λ)`. Polynomials in `T_a` commute, so both orders
  hold. Hence `D̃(λ)` is invertible where `R(λ) ≠ 0`, and there
  `R(λ) D̃(λ)^{−1} = v(T_a, λ)`, which is holomorphic in `λ`.
- The journal prints this formula as `R(λ)D̃(λ)^{−1} = v(T_a, λ)g(T_a, λ)`. The extra factor
  `g(T_a, λ)` is a typographical slip. By the identity just derived, `v(T_a, λ) g(T_a, λ)` is
  the scalar `R(λ)` on `𝒜_Q(wμ_P)`.
- BL then write `M(w, λ)φ = D̃(λ)^{−1}(D(λ)((C_{G,Q} E(φ, λ))_{−wλ}))` and conclude "this
  provides meromorphic continuation of `M(w, λ)φ`". In other words,
  `R(λ) M(w, λ)φ = v(T_a, λ) D(λ)((C_{G,Q} E(φ, λ))_{−wλ})`.
- §8.2, p. 222, Lemma: for fixed `φ`, the forms `M(w, λ)φ` lie in one finite-dimensional
  subspace of `𝒜_Q` that does not depend on `λ`. This lemma is cited only for comparison
  below. The proof here does not use it.
- §3.1, p. 192, for meromorphy with values in a locally convex space.

## Proof, as implemented

**Translation operators.** `leftTranslationEnd t` is `ψ ↦ (x ↦ ψ(t x))` as a `ℂ`-linear
endomorphism of the functions on a group. A polynomial `p` acts through `Polynomial.aeval`. So
products of polynomials act by composition, and constants act as scalars.
`aeval_leftTranslationEnd_apply` evaluates `p(T_t)ψ(x)` as
`∑_{k < B} p_k ψ(t^k x)` for any `B > natDegree p`. `isTranslationPolynomialSolution_iff`
identifies the Library predicate `IsTranslationPolynomialSolution t p ψ` with `p(T_t)ψ = 0`.

**Recovery identity.** Take `f` and roots `r_1, …, r_k`, and set
`W = ∏ j (f(r_j) − f)` and `den = ∏ j f(r_j)`. `recoveryPolynomial_spec` proves two facts.
First, `W = den + h f` for some `h`: modulo `f`, each factor is the constant `f(r_j)`. Second,
`W = h' ∏ j (X − r_j)`: each `X − r_j` divides `f − f(r_j)`. `aeval_recoveryPolynomial`
deduces the following. If `f(T)ψ = 0` and `∏ j (T − r_j)(Φ − ψ) = 0`, then
`W(T)Φ = W(T)ψ + W(T)(Φ − ψ) = den · ψ + 0`.

This replaces BL's resultant. With `g = ∏ j (X − r_j)`, the polynomial `W` is
`v' g` for `v' = ∏ j (−q_j)`, where `f − f(r_j) = q_j (X − r_j)`. The scalar `den` equals BL's
resultant `R(λ)` up to sign and a power of the leading coefficient of `f`. It is nonzero
exactly when `f` and `g` are coprime.

**Entire coefficients.** `entireSubalgebra m` is the subalgebra of entire functions on `ℂᵐ`.
`differentiable_coeff_recoveryPolynomial` forms `W` over this subalgebra and evaluates at each
point. This shows that the coefficients of `∏ j (f(r_j(s)) − f)` are entire in `s` when the
`r_j` are.

**The case `N = 0`.** A closed subgroup of `GL_0` has trivial adelic points
(`subsingleton_adelicGroupPoints_of_rank_zero'`, the universe-polymorphic form of a published
lemma). Then every height is the height of `1 ∈ K`, which is `0`, so every height power is `1`
(`IsIwasawaCompact.heightPower_eq_one_of_subsingleton`). Unfolding the operator, its integrand
and the twist, `M(w, λ)φ` does not depend on `λ`. The witnesses are `E = M(w, ·)φ`, `D` the
whole space and `R₀ = 0`. Constant functions are meromorphic in coordinates
(`isMeromorphicInCoordinatesOn_const`). The parameter space is finite-dimensional by
`rationalCharacters_free_finite`. Neither premise is used in this case.

**The case `N > 0`.**

1. Apply both premises to the given data. This yields:
   - the continuation `E'`, equal to `E(φ, λ)` for `R₁`-regular `λ`, with local Fréchet-valued
     meromorphic presentations;
   - `t`, `f`, `root`, `λ₀` and `R₂`.

   The space `V(F) \ V(𝔸)` is compact (`compactSpace_rationalQuotient_range_unipotent`, for
   the smooth connected unipotent `V`). Fix the coordinates `e₀ : ℂᵐ ≃ X^*(P) ⊗ ℂ` given by
   `Module.finBasis`.
2. Local data for the constant terms. The scalar functions `s ↦ C_Q E'(e₀ s)(y)`, `y ∈ G(𝔸)`,
   have local meromorphic data with denominators independent of `y`. Near `s₀` take the
   presentation `f_loc` with values in the Fréchet space `𝔉^R_L`. The constant-term
   evaluation at `y` is a continuous linear form on `𝔉^R_L`
   (`UniformGrowthFrechetSpace.constantTermEvaluation`), so
   `hasLocalMeromorphicData_of_isMeromorphicOn` applies.
3. The recovered family. Write `λ = e₀ s` and
   `Φ_s(y) = m_Q(y)^{−wλ} C_Q E'(λ)(y)`. Let `W_s` and `den(s)` be the recovery polynomial and
   denominator of `f` and the roots `root j λ`. Put `Ψ_x(s) = den(s)^{−1} (W_s(T_t) Φ_s)(x)`.
   This is
   `den(s)^{−1} ∑_{n < B} (W_s)_n · m_Q(t^n x)^{−wλ} · C_Q E'(λ)(t^n x)` with
   `B = k · deg f + 1`. Its ingredients are as follows:
   - the coefficients `(W_s)_n` are entire;
   - the height powers are exponentials of linear forms in `s`;
   - `den` is entire and nonzero at `e₀^{−1} λ₀` by the premise.

   `HasLocalMeromorphicData.combination` gives local data for the family `Ψ_x`, `x ∈ G(𝔸)`,
   and `exists_isMeromorphicOn_pi_of_local` glues them. The result is a set `U₀` such that
   `s ↦ (Ψ_x(s))_x` is meromorphic with values in `G(𝔸) → ℂ`, for the product topology, with
   domain of holomorphy `U₀`.
4. The witnesses. Put `R₀ = max R₁ R₂`. Let `E(λ)` be `M(w, λ)φ` for `R₀`-regular `λ`, and
   `(Ψ_x(e₀^{−1} λ))_x` otherwise. Let `D = e₀(U₀ ∩ {den ≠ 0})`. Then `E` agrees with
   `M(w, λ)φ` on the regular region by definition. On `U₀ ∩ {den ≠ 0}`, `E ∘ e₀` equals the
   glued function `s ↦ (Ψ_x(s))_x`. Off the regular region this holds by definition. On it,
   `E'(λ) = E(φ, λ)`, so `Φ_s` is the function of the premise. The recovery identity then gives
   `W_s(T_t) Φ_s = den(s) · M(w, λ)φ`, and `den(s) ≠ 0` gives `Ψ_x(s) = M(w, λ)φ(x)`. The set
   `U₀ ∩ {den ≠ 0}` is open and dense, so `IsMeromorphicOn.congr_mono` transfers meromorphy.
   `isMeromorphicInCoordinatesOn_of_coordinates` passes from the coordinates `e₀` to all linear
   coordinate systems.

Axioms used: `propext`, `Classical.choice`, `Quot.sound`.

## Differences from BL's argument

- BL invert the restriction `D̃(λ) = g(λ, T_a)` on the exponent space `𝒜_Q(wμ_P)`, which
  `f(T_a)` annihilates, by evaluating the Bézout identity `u f + v g = R` there. Their
  recovery formula is `R(λ) M(w, λ)φ = v(T_a, λ) D(λ)((C_{G,Q} E(φ, λ))_{−wλ})`.
- The proof here never uses that space. It applies `W_s(T_t)` to arbitrary functions on
  `G(𝔸)`, and only the two annihilation identities of the premise are needed. Here
  `W_s = v' g` with `g = ∏ j (X − r_j)`, and `W_s ≡ den(s)` modulo `f`. So
  `W_s(T_t) = v'(T_t) g(T_t)` plays the role of BL's `v(T_a, λ) D(λ)`, and `den(s)` plays the
  role of `R(λ)`. The resulting formula is `den(s) M(w, λ)φ = W_s(T_t) Φ_s`.
- No finiteness property is used. In particular, the proof does not use the §8.2 Lemma, and
  it does not need `𝒜_Q(wμ_P)` to be finite-dimensional.
- The continuation constructed here is the recovered family off the regular region.
  Meromorphy in the topology of pointwise convergence holds with local denominators equal to
  those of the Eisenstein continuation times `den`. These do not depend on `g ∈ G(𝔸)`.

## Scope

- Neither premise is proved here, so the target is not proved by this module.
  - `EisensteinMeromorphicContinuationStatement` is reduced to two further statements in
    `AdelicEisensteinContinuationReduction`.
  - `IntertwiningConstantTermDifferenceStatement` is new. Its proof needs the constant-term
    formula (`EisensteinConstantTermStatement`), the exponents of
    `M(w, λ)φ` and of the other terms of (6.17), and BL's Lemma on regular `a ∈ A_Q`.
- The case `N = 0` of the target is proved unconditionally inside the theorem.
- Nothing is claimed about the location of singularities, holomorphy on the regular region or
  uniqueness of the continuation.
