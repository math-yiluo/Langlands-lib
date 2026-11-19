# Continuation from a Mellin pair identity (core of Jacquet 2009, Proposition 4.1)

This is an intermediate result of Task 7400, towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. Authored by
Worker 823. Every declaration is proved, with no axioms beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`). The module imports only Mathlib.

The module proves the analytic core of Proposition 4.1 of Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), pp. 23–25. Suppose two integrals `∫ F δ^s dμ` and `∫ F' δ'^s dμ'` converge
for `Re s ≥ N`. Fix one pair of rapidly decreasing functions `(h, k)` whose Mellin transforms
`mellin h (-s)` and `mellin k (-s)` are both nonzero on a common right half-plane
`σ₁ < Re s`. Suppose the two integrals are linked by Jacquet's theta identity (4.1) for this
pair. Then both integrals have meromorphic continuations. The nonvanishing hypothesis is
essential: the continuations are obtained by dividing by these Mellin transforms, and
convergence together with the theta identity alone does not give a continuation (for the
zero pair `h = k = 0` the theta identity holds trivially). If in addition the Mellin
transforms of `h` and `k` satisfy a factor identity, the continuations satisfy a functional
equation. The conclusion has the shape of the continuation and functional-equation conjuncts of
the Library's `RealJacquet.EquationPackage` (module `RealJacquetConventionReduction`).

Notation. In Mathlib, `mellin f s = ∫ t in Ioi 0, t ^ (s - 1) • f t`. So `mellin f (-s)` is
`∫₀^∞ f(t) t^(-s) dt/t`.

## The statement

`Langlands.Global.RankinSelbergGlobal.MellinPairContinuationStatement.{u, v} : Prop` says the
following. Let the data be:
- measurable spaces `X : Type u` and `X' : Type v` with s-finite measures `μ`, `μ'`;
- functions `F : X → ℂ` and `F' : X' → ℂ`, a.e. strongly measurable for `μ` and `μ'`;
- measurable functions `δ : X → ℝ` and `δ' : X' → ℝ` with `δ x > 0` and `δ' x > 0` for all `x`;
- measurable functions `h, k : ℝ → ℂ` satisfying `RapidDecay`. Here `RapidDecay h` means: for
  every real `M` there is `C` with `‖h t‖ ≤ C · t ^ M` for all `t > 0`;
- real numbers `N`, `σ₁`, functions `Z, Zd, L, Ld, E : ℂ → ℂ`, and a constant `sign : ℂ`.

Write `θ(a) = theta μ F δ h a = ∫ F(x) h(a δ(x)) dμ(x)` and
`θ'(a) = theta μ' F' δ' k a = ∫ F'(x) k(a δ'(x)) dμ'(x)`. Assume:
1. (convergence) for every real `σ ≥ N`, the functions `x ↦ ‖F x‖ δ(x)^σ` and
   `x ↦ ‖F' x‖ δ'(x)^σ` are integrable;
2. (pair identity) `θ(a) = a · θ'(a⁻¹)` for every real `a > 0`;
3. (nonvanishing) `mellin h (-s) ≠ 0` and `mellin k (-s) ≠ 0` whenever `σ₁ < Re s`;
4. (the integrals) `Z s = ∫ F(x) δ(x)^s dμ` and `Zd s = ∫ F'(x) δ'(x)^s dμ'` whenever
   `N ≤ Re s`;
5. (factor identity) for `s` outside a discrete closed subset of `ℂ` (the filter
   `codiscrete ℂ`):
   `L s · mellin h (-s) = sign · E s · Ld (1 - s) · mellin k (s - 1)`.

Then there are `σ : ℝ` and `M, Md : ℂ → ℂ` such that:
- `M` and `Md` are meromorphic on all of `ℂ`;
- `Z s = M s` and `Zd s = Md s` whenever `σ < Re s`;
- for `s` outside a discrete closed subset of `ℂ`,
  `L s · Md (1 - s) = sign · E s · Ld (1 - s) · M s`.

The theorem `Langlands.Global.RankinSelbergGlobal.mellinPairContinuation` proves it. The proof
takes `σ = max N σ₁`.

## Proof structure

The declarations below, except the last two, are in the namespace
`Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinPair`.

### Rapidly decreasing functions

- `RapidDecay h`: the definition above.
- `RapidDecay.comp_mul_right`: `t ↦ h(t c)` is rapidly decreasing for `c > 0`.
- `RapidDecay.nonneg_const`: a bound `‖h t‖ ≤ C t^M` for all `t > 0` forces `C ≥ 0`.
- `RapidDecay.integrableOn`: for measurable `h`, `t ↦ t^σ ‖h t‖` is integrable on `(0, ∞)` for
  every real `σ`. On `(0, 1]` the bound with `M = -σ` makes the integrand bounded. On `(1, ∞)`
  the bound with `M = -σ - 2` dominates it by `C t^(-2)`.
- `RapidDecay.mellinConvergent`: hence `MellinConvergent h s` for every `s`.
- `RapidDecay.isBigO`: `h = O(t^M)` along any filter on which `t > 0` eventually.
- `RapidDecay.differentiable_mellin`: for a.e. strongly measurable rapidly decreasing `g`,
  `mellin g` is entire. At each `s` this applies Mathlib's
  `mellin_differentiableAt_of_isBigO_rpow` with the bounds `O(t^(-(Re s + 1)))` at `∞` and
  `O(t^(-(Re s - 1)))` at `0`. Local integrability on `(0, ∞)` comes from the bound with `M = 0`.
- `rapidDecay_of_bounds`: separate rapid-decay bounds on `(0, 1]` and on `[1, ∞)` give
  `RapidDecay`.

### The theta function

- `integral_rpow_mul_norm_comp_mul_right`: the change of variables
  `∫₀^∞ t^(-σ-1) ‖h(t c)‖ dt = c^σ ∫₀^∞ t^(-σ-1) ‖h t‖ dt` for `c > 0`.
- `norm_integral_le`: if `‖h t‖ ≤ C t^M` for `t > 0` and `‖F‖ δ^M` is integrable, then
  `‖∫ F(x) h(a δ(x)) dμ‖ ≤ C a^M ∫ ‖F‖ δ^M dμ` for `a > 0`.
- `aestronglyMeasurable_theta`: `a ↦ ∫ F(x) h(a δ(x)) dμ` is a.e. strongly measurable for any
  s-finite measure on `ℝ`. This is `AEStronglyMeasurable.integral_prod_right'`.
- `theta μ F δ h a := ∫ F(x) h(a δ(x)) dμ(x)` (Jacquet's `θ(a)`, p. 24).
- `theta_bound`: from `norm_integral_le`, `‖θ(a)‖ ≤ C a^M` for `a > 0`, with `C ≥ 0`, whenever
  `‖F‖ δ^M` is integrable.

### Mellin transform of theta by Fubini

`mellin_theta`: if `x ↦ ‖F x‖ δ(x)^(Re s)` is integrable, then
`mellin θ (-s) = (∫ F(x) δ(x)^s dμ) · mellin h (-s)`.

The proof applies `integral_integral_swap` to
`G(a, x) = a^(-s-1) F(x) h(a δ(x))` on `(volume restricted to (0, ∞)) × μ`. Integrability of `G`
uses `integrable_prod_iff'`:
- for each `x`, `a ↦ G(a, x)` is integrable, by `RapidDecay.mellinConvergent` applied to
  `t ↦ h(t δ(x))`;
- `x ↦ ∫ ‖G(a, x)‖ da` equals `‖F x‖ δ(x)^(Re s) ∫₀^∞ t^(-Re s - 1) ‖h t‖ dt`, by
  `integral_rpow_mul_norm_comp_mul_right`. This is integrable by hypothesis.

The inner integral in `a` is `F(x) δ(x)^s mellin h (-s)`, by Mathlib's `mellin_comp_mul_right`.

### The two-sided argument

- `theta_rapidDecay`: under hypotheses 1 and 2, `θ` is rapidly decreasing. Near `0`,
  `theta_bound` with exponent `max N M` gives `‖θ(a)‖ ≤ C a^M` for `0 < a ≤ 1`. Near `∞`, the
  pair identity gives `‖θ(a)‖ = a ‖θ'(a⁻¹)‖`. Then `theta_bound` for `θ'` with exponent
  `max N (1 - M)` gives `‖θ(a)‖ ≤ C a^(1 - max N (1 - M)) ≤ C a^M` for `a ≥ 1`.
- `mellin_theta_entire` (the core of Proposition 4.1). Under hypotheses 1 and 2, with
  `Θ(s) = mellin θ (-s)`:
  - `Θ` is entire, by `RapidDecay.differentiable_mellin` for `θ`;
  - `Θ(s) = (∫ F δ^s dμ) · mellin h (-s)` for `Re s ≥ N`, by `mellin_theta`;
  - `Θ(s) = (∫ F' δ'^(1-s) dμ') · mellin k (s - 1)` for `Re s ≤ 1 - N`. By the pair identity,
    `θ` agrees on `(0, ∞)` with `a ↦ a^1 • θ'(a⁻¹)`. Mathlib's `mellin_cpow_smul` and
    `mellin_comp_inv` turn `mellin θ (-s)` into `mellin θ' (-(1 - s))`, and `mellin_theta` for
    `θ'` at `1 - s` gives the formula.
- `exists_continuation`: the statement above, in theorem form. Take `σ = max N σ₁` and
  - `M(s) = Θ(s) / mellin h (-s)`;
  - `Md(s) = Θ(1 - s) / mellin k (-s)`.

  Both are quotients of entire functions, hence meromorphic. For `Re s > σ`:
  - `M(s) = Z(s)` by the first formula for `Θ` and hypothesis 3;
  - `Md(s) = Zd(s)` by the second formula for `Θ` at `1 - s` and hypothesis 3.

  For the functional equation, `Md(1 - s) = Θ(s) / mellin k (s - 1)`. Hypothesis 3 gives a point
  where the entire function `s ↦ mellin h (-s)` does not vanish. By
  `AnalyticOnNhd.preimage_zero_mem_codiscrete`, its zeros therefore form a codiscrete
  complement, and likewise for `s ↦ mellin k (s - 1)`. Off these zeros, and where the factor
  identity 5 holds, the equation is the factor identity multiplied by `Θ(s)` and divided by
  both Mellin transforms.

In the namespace `Langlands.Global.RankinSelbergGlobal`:
- `MellinPairContinuationStatement.{u, v}`: the proposition stated above;
- `mellinPairContinuation`: its proof, by `exists_continuation`.

## Relation to the literature

Jacquet, *Archimedean Rankin–Selberg integrals* (2009):
- §4.1, p. 22: the Mellin transform `∫ f(x) |x|_F^s d^×x` on `F^×`;
- §4.2, pp. 22–23: `(σ, ψ)` pairs and their scaling property;
- §4.3, pp. 23–25: Proposition 4.1 and its proof.

**Jacquet's proposition.** Let `σ` be a representation of the Weil group. Let `f, f'` be
measurable on `F^×` with `∫ |f(x)| |x|^s d^×x` and `∫ |f'(x)| |x|^s d^×x` finite for `s ≥ N`.
Assume that `∫ f h d^×x = ∫ f' k d^×x` for every `(σ, ψ)` pair `(h, k)`. Then:
- the Mellin transforms of `f` and `f'` extend to holomorphic multiples of `L(s, σ)` and
  `L(s, σ̃)`, bounded at infinity in vertical strips;
- `∫ f'(x) |x|^(1-s) d^×x / L(1 - s, σ̃) = ε(s, σ, ψ) ∫ f(x) |x|^s d^×x / L(s, σ)` holds in the
  sense of analytic continuation.

A `(σ, ψ)` pair (p. 22) is a pair `h, k ∈ S(F^×)`, both depending only on `|t|_F`, with
`∫ h(t) |t|^(-s) d^×t = ε(s, σ, ψ) e^(P(s)) / L(s, σ)` and
`∫ k(t) |t|^(-s) d^×t = e^(P(1-s)) / L(s, σ̃)`. Here `P` is a quadratic polynomial of the
form `P(s) = A s² + B s + C` with `A > 0`, `B ∈ ℝ` and `C ∈ ℂ`; Jacquet asserts that such a
pair exists for every such `P`.

**Jacquet's proof.** On p. 24 Jacquet sets `θ(a) = ∫ f(x) h(a x) d^×x`. He applies the
hypothesis to the scaled pair `(x ↦ h(a x), x ↦ |a| k(a⁻¹ x))`, which is again a `(σ, ψ)` pair
(p. 23), and obtains (4.1): `θ(a) = |a| ∫ f'(x) k(a⁻¹ x) d^×x`. The proof then has four steps:
- `θ` is rapidly decreasing at both ends, so `∫ θ(a) |a|^(-s) d^×a` is entire;
- for `Re s` large this integral is `∫ f |x|^s d^×x · ∫ h |a|^(-s) d^×a`;
- for `Re s` small it is `∫ f' |x|^(1-s) d^×x · ∫ k |a|^(-(1-s)) d^×a`;
- dividing by the Mellin transforms of the pair gives the continuation and the functional
  equation.

The Lean proof follows these steps in this order.

**Differences from Jacquet.**
- *Measure space.* Lean works on an arbitrary s-finite measure space `(X, μ)` with a positive
  measurable function `δ`, in place of `F^×` with `d^×x` and `|x|_F`. Jacquet's setting is the
  case `X = F^×`, `μ = d^×x`, `δ(x) = |x|_F`, with Lean's `F, F'` (functions) equal to Jacquet's
  `f, f'`; Jacquet's `F` is the field `ℝ` or `ℂ`. The functions `h, k` are functions of `t > 0`, matching
  Jacquet's remark that a pair depends only on `|t|_F`. The general form is meant to allow
  `X` to be a quotient such as `N\GL_n` with `δ = |det|`, but this module does not carry out
  any such application.
- *Hypothesis on `(h, k)`.* Lean assumes the identity (4.1), as `θ(a) = a · θ'(a⁻¹)` for
  `a > 0`, for one fixed pair `(h, k)`. In the case `X = F^×`, Jacquet's `θ(a)` is Lean's
  `θ(|a|_F)`, and (4.1) reads `θ(|a|_F) = |a|_F · θ'(|a|_F⁻¹)`. Jacquet assumes `∫ f h = ∫ f' k` for every pair and
  derives (4.1). Lean replaces `h, k ∈ S(F^×)` by measurability and the size condition
  `RapidDecay`, which is the bound Jacquet uses at the start of his proof (p. 24).
- *Mellin normalization.* Lean uses Mathlib's `mellin` on `(0, ∞)` with `dt/t`. For a radial
  function on `F^×`, Jacquet's `∫_(F^×) h(|t|_F) |t|_F^(-s) d^×t` equals `c · mellin h (-s)`.
  Here `c > 0` depends only on `F` and the normalization of `d^×t`.
- *Factor identity.* Lean takes the factor identity (hypothesis 5) and the nonvanishing of the
  two Mellin transforms (hypothesis 3) as hypotheses. It does not mention `σ` or `ψ`. For a
  `(σ, ψ)` pair both hold, by the following derivation, which is not formalized here. Jacquet's
  formulas give `mellin h (-s) = c⁻¹ ε(s, σ, ψ) e^(P(s)) / L(s, σ)` and, at `1 - s`,
  `mellin k (s - 1) = c⁻¹ e^(P(s)) / L(1 - s, σ̃)`. Hence
  `L(s, σ) · mellin h (-s) = ε(s, σ, ψ) · L(1 - s, σ̃) · mellin k (s - 1)` away from the
  poles. This is hypothesis 5 with `L = L(·, σ)`, `Ld = L(·, σ̃)`, and `sign · E s = ε(s, σ, ψ)`.
  For `Re s` large, `mellin h (-s)` and `mellin k (-s) = c⁻¹ e^(P(1-s)) / L(s, σ̃)` are both
  nonzero: the exponentials and `ε(s, σ, ψ)` never vanish, and the `L`-factors have no poles
  there.
- *Conclusion.* Lean proves meromorphic continuation and the multiplied-out functional
  equation `L(s) · Md(1 - s) = sign · E(s) · Ld(1 - s) · M(s)` off a discrete closed set. This is
  the shape of `RealJacquet.EquationPackage`. Jacquet's equation multiplied by
  `L(s, σ) L(1 - s, σ̃)` has this shape, with `sign · E(s) = ε(s, σ, ψ)`.

**Not proved here.**
- That the continuations are holomorphic multiples of the `L`-factors, and their boundedness in
  vertical strips (Jacquet's Phragmén–Lindelöf argument and Lemma 4.2, pp. 25–26).
- The existence of `(σ, ψ)` pairs (Jacquet p. 22–23 uses an inverse Mellin transform and
  bounds on `L`-factors in vertical strips).
- Any instance of the pair identity for Rankin–Selberg integrals.
