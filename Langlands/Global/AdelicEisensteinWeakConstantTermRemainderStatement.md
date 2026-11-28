# The remainder of the weak constant term of Eisenstein series: exponents on cones

Module `Langlands.Global.AdelicEisensteinWeakConstantTermRemainderStatement`, namespace
`Langlands.Global`. It defines one predicate, `HasConeShiftEquations`, and states one
proposition, `EisensteinWeakConstantTermRemainderStatement`. It proves nothing.

## Source

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF; PDF page = printed page).

- §4.1, p.16: the weak constant term (4.3),
  `E_P(·, φ, λ)^w_Q = ∑_{s ∈ W(P, Q)} E^Q_{Q_s}(·, M(s, λ) φ, s λ)`, holomorphic in a
  neighborhood of `i𝔞_P^*`. p.17: `E^-_Q = E_Q − E^w_Q` is holomorphic there too, its exponents
  lie in `𝓔^-_Q(λ) = ∪_{s ∈ W(Q\G/P) \ W(P, Q)} {s(𝓔_{P_s}(φ) + λ)|_{𝔞_Q}}` for all
  `λ ∈ i𝔞_P^*` "by analyticity", and (4.4): `X ↦ E^-_Q(exp X g)` on `𝔞_Q` is an exponential
  polynomial whose exponents form a list `𝓔̃^-_Q(λ)` built from `𝓔^-_Q(λ)` by repetitions; the
  real parts of these exponents do not depend on `λ ∈ i𝔞_P^*`.
- §5.1, pp.18–19, proof of Lemma 5.1: the polynomial bound (5.1) on Siegel sets, and the fact
  that the exponents `μ` of `φ_Q − φ^w_Q` have real part `∑_{α ∈ Δ_Q} c_α α` with `Re c_α ≤ 0`
  and some `Re c_α ≠ 0`, so that `Re μ(Y) < −ε'` on the unit vectors `Y` of the cone
  `𝔞^{G,+}_{Q,δ} = {Y ∈ 𝔞^{G,+}_Q : α(Y) ≥ δ‖Y‖, α ∈ Δ_Q}`. pp.19–20, proof of Lemma 5.3: the
  same for Eisenstein series, using Proposition 4.1 (p.17), the independence of the real parts
  of the exponents from `λ ∈ i𝔞_P^*` and (4.3).

E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series* (Clay
Math. Proc. 13, 2011), registered as `lapid-2011-asymptotic-inner-product-truncated-eisenstein`
(PDF page = printed page + 9):

- printed p.322: the decomposition (12) of the constant term of `E_P(φ, λ)` along `Q` as
  `M_Q + E_Q` (Lapid's `M_Q` is Delorme's `E^w_Q`, Lapid's `E_Q` is Delorme's `E^-_Q`), and the
  description (13) of the exponents of the second term.
- printed pp.322–323, Lemma 6: `Re ⟨w μ, ϖ^∨⟩ ≤ 0` for the exponents `w μ` in (13) and the
  fundamental coweights `ϖ^∨` of `Q_w`, with `Re w μ = 0` only for `w ∈ Ω(P; Q)`.
- printed p.323, Corollary 2: outside the singular hyperplanes the exponent multisets of
  `M_Q` and `E_Q` have size at most a constant `k`; the real parts of the exponents of `E_Q`,
  over all `λ ∈ i𝔞_P^*`, form a finite subset of the closure of the negative cone that does not
  contain `0`.

## The predicate `HasConeShiftEquations`

`HasConeShiftEquations F G T i ν T₀ j J δ ε m f` concerns a function `f : G(𝔸) → ℂ`, a set `J`
of characters of `T`, reals `δ, ε` and `m : ℕ`. Write `Δ = simpleRelativeRoots i ν`, `A_{T₀}`
for the positive points of `T₀` (`PositiveRealTorus.intrinsicSubgroup F T₀`), `a ↦ a` also for
their images in `G(𝔸)` (`positiveMap F G T i T₀ j`), `|χ(a)|` for the normalized idele norm of
`j ≫ χ` at `a` (so `logNormHom F T₀ a (j ≫ χ) = log |χ(a)|`) and `δ(a) = siegelModulus a`.

The predicate holds when, for every `a ∈ A_{T₀}` with

- `log |β(a)| = 0` for every `β ∈ J`,
- `0 ≤ log |α(a)|` for every `α ∈ Δ \ J`, and
- `δ log |α'(a)| ≤ log |α(a)|` for all `α, α' ∈ Δ \ J`,

there are `w_0, …, w_{m-1} ∈ ℂ` with `|w_k| ≤ δ(a)^{1/2} e^{−ε log |α(a)|}` for every `k` and every
`α ∈ Δ \ J`, such that `∑_k c_k f(a^k g) = 0` for every `g ∈ G(𝔸)`, where
`∏_k (X − w_k) = ∑_k c_k X^k` (`IsTranslationPolynomialSolution`).

For `J ⊆ Δ` the points `a` are the points of `A_{T₀}` lying in the split component `𝔄_Q` of the
standard parabolic `Q = Q_J`, and the second and third conditions say that `H_Q(a)` lies in the
closed cone of `𝔞_Q^G` on which the simple roots outside `J` are nonnegative and comparable
with ratio `δ`. This is Delorme's cone `𝔞^{G,+}_{Q,δ'}` for a `δ'` depending on `δ`, because the
restrictions of the `α ∈ Δ \ J` are a basis of the dual of `𝔞_Q^G`. On `𝔄_Q` the Siegel modulus
`δ(a)` is the modulus `δ_Q(a)` of `Q`, because the roots of the Levi subgroup of `Q` are trivial
there. The predicate is the difference-equation form of an exponent condition: if `f = ∑_μ f_μ`
is a finite sum of functions with normalized exponents `μ` along `𝔄_Q`, that is
`f_μ(a g) = a^{μ + ρ_Q} p_g(H_Q(a))` with polynomials `p_g` of degree at most `d_μ`, and
`∑_μ (d_μ + 1) ≤ m`, then `∏_μ (L_a − a^{μ + ρ_Q})^{d_μ + 1}` annihilates `f`. The roots
have absolute value `|a^{μ + ρ_Q}| = e^{Re μ(H_Q(a))} δ_Q(a)^{1/2}`, so the bound on the roots
says that `Re μ(H_Q(a)) ≤ −ε log |α(a)|` for every `α ∈ Δ \ J`, a strictly negative real part
on the cone. Further roots `0` fill up the list to length `m`.

## The statement

The data are exactly those of `EisensteinConstantTermWeakApproximationStatement`
(`Langlands/Global/AdelicEisensteinConstantTermWeakApproximationStatement.md`, "The
statement"), in the same order: a number field `F : Type`, a connected reductive `G`, a presented
parabolic `P` with geometric unipotent radical, a maximal compact `K` with `P(𝔸)K = G(𝔸)`, a closed
matrix embedding `rho`, `φ ∈ A^2_P`, a pointwise continuation `(E, D)` of the Eisenstein series
of `φ` with `D ⊇ i𝔞_P^*`, coordinates `e : ℝⁿ ≃ X^*(P) ⊗ ℝ`, a compact `C ⊆ ℝⁿ`, an algebraic
Siegel setup `(T, i, ν, T₀, j)` with `K` Iwasawa for its minimal parabolic, a proper subset `J`
of `Δ` with `hKQ : IsIwasawaCompact (Standard.parabolicHom i ν J) K`, `δ > 0`, a threshold `t`
and a compact `Ω ⊆ G(𝔸)`.

Conclusion: there are `ε > 0`, `m : ℕ`, `B`, `k : ℕ` and for each `q < k` a function
`c_q : ℝⁿ → ℂ`, a subspace `V_q ⊆ ℝⁿ`, a real linear map `L_q : V_q → X^*(Q) ⊗ ℝ` and a function
`Φ_q : ℝⁿ → G(𝔸) → ℂ` such that items 1–6 of `EisensteinConstantTermWeakApproximationStatement`
hold: `ε > 0`; each `c_q` is smooth; each `L_q` is surjective;
`Φ_q(x + v, g) = m_Q(g)^{i L_q(v)} Φ_q(x, g)` for `v ∈ V_q`; `x ↦ Φ_q(x, g)` is continuous; and
`‖Φ_q(x, z b ω)‖ ≤ B δ(b)^{1/2} σ(z b ω)^m` for `x ∈ C`, `z ∈ A_G`, `b` in the weak simple-root
chamber `|β(b)| ≥ t` of `A_{T₀}` and `ω ∈ Ω`. Moreover, for every `x ∈ C` the remainder

`r_x(g) = E(i e(x))_Q(g) − ∑_q c_q(x) Φ_q(x, g)`,

where `E(i e(x))_Q = subgroupConstantTerm F (Standard.unipotentHom i ν J) (E (i e(x)))` is the
constant term along the unipotent radical of `Q = Q_J`, satisfies:

7a. `‖r_x(z g)‖ = ‖r_x(g)‖` for `z ∈ A_G` (`RestrictionSplitCentre.canonicalSubgroup F G`) and
    `g ∈ G(𝔸)`;
7b. `‖r_x(b ω)‖ ≤ B δ(b)^{1/2} σ(b ω)^m` for `b` in the weak simple-root chamber of threshold `t`
    and `ω ∈ Ω`;
7c. `HasConeShiftEquations F G T i ν T₀ j J δ ε m r_x`.

Here `δ = siegelModulus`, `σ = adelicLogHeight` and `m_Q(g)^λ = hKQ.heightPower λ g`.

## Why the statement is true

Take `P` standard and `K` in good position, as in Delorme; the transfers to arbitrary presented
parabolics, compact subgroups and Siegel setups are those described in
`AdelicEisensteinWeakConstantTermApproximationStatement.md` ("Transfers").

- **Items 1–6.** The weak constant term (4.3) supplies the triples, exactly as described for
  `EisensteinWeakConstantTermApproximationStatement`: `Φ_q(x, ·)` is the relative Eisenstein
  series `E^Q_{Q_s}(·, ψ_{s,l}, s i e(x))` of a basis vector `ψ_{s,l}` of the finite-dimensional
  space containing the vectors `M(s, λ) φ`, and `c_q(x)` is the coefficient of `M(s, i e(x)) φ`
  along `ψ_{s,l}`. Then `∑_q c_q(x) Φ_q(x, ·) = E^w_Q` at `λ = i e(x)`, and `r_x = E^-_Q`.
- **7a.** `φ` is `A_P`-equivariant (`IsSplitComponentEquivariant`), so `E(φ, λ)(z g) =
  e^{λ(H_G(z))} E(φ, λ)(g)` for `z ∈ A_G`, and the same holds for the constant term. Each term of
  (4.3) transforms under `A_G` by `e^{(sλ)(H_G(z))} = e^{λ(H_G(z))}`, because each `s ∈ W(P, Q)`
  fixes `𝔞_G`. For `λ ∈ i𝔞_P^*` this character is unitary.
- **7b.** This is the polynomial bound (5.1) for `E^-_Q`, for `X ∈ 𝔞_0^+` and with the factor
  `(1 + ‖X‖)^d` written through `σ`. For `E_Q` it follows from Proposition 4.1: the constant term
  averages `E` over the compact quotient `N_Q(F) \ N_Q(𝔸)`, and conjugation by the inverse of a
  chamber point keeps a compact set of representatives in a compact set (the Library's
  `StandardParabolicFamily.hasSiegelChamberGrowth_constantTerm` carries out this averaging for
  bounds of the form `δ(b)^{1/2} (1 + log H(b))^m`). For `∑_q c_q Φ_q` it follows from item 6
  with `z = 1`, since the `c_q` are bounded on the compact `C`.
- **7c.** By (4.4), Lapid's (13) and Delorme's analyticity argument (p.17), `r_x` is a finite sum
  of terms `f_μ` with normalized exponents `μ ∈ 𝓔̃^-_Q(i e(x))` along `𝔄_Q`, with `∑ (d_μ + 1)`
  bounded independently of `x ∈ C` (Lapid's Corollary 2 at regular parameters). By Lapid's
  Lemma 6 and Corollary 2 the real parts `Re μ` lie in a finite set, independent of `x`, of
  nonzero linear forms `∑_{α ∈ Δ \ J} c_α α|_{𝔞_Q}` with all `c_α ≤ 0` (the real parts vanish on
  `𝔞_G` by 7a). For `a` as in `HasConeShiftEquations`, `⟨α, H_Q(a)⟩ = log |α(a)|`, and some
  `c_{α*} < 0`, so `Re μ(H_Q(a)) ≤ c_{α*} log |α*(a)| ≤ c_{α*} δ log |α(a)|` for every
  `α ∈ Δ \ J`. This gives a common `ε > 0`, and the computation in the previous section gives
  the shift equations. At an imaginary parameter on a singular hyperplane, `E^-_Q` is the
  pointwise limit of its values at nearby regular parameters (it is holomorphic there,
  Delorme p.17). Along a convergent subsequence of the root lists, which are bounded, the shift
  equations and the bounds on the roots pass to the limit, since each equation involves finitely
  many values of the function.

## Use

The Library's `Langlands.Global.eisensteinConstantTermWeakApproximation_of_remainder` (module
`Langlands.Global.AdelicEisensteinConstantTermWeakApproximationReduction`) proves that this
statement implies `EisensteinConstantTermWeakApproximationStatement`: in Delorme's proof of
Lemma 5.1, the shift equations take the place of Lapid's Lemma 3 and the passage of Lemma 5.2 to
the cone.

## Scope

The statement does not identify `∑_q c_q Φ_q` with the weak constant term, and it does not assert
(4.3), (4.4) or Lapid's Lemma 6 themselves. It asserts the existence of triples with items 1–6
and a remainder with properties 7a–7c. The bound 7b is asserted with `z = 1` only; together with
7a it holds for every `z ∈ A_G` with `σ(b ω)` in place of `σ(z b ω)`. For empty `Ω` the bounds of
item 6 and 7b are vacuous. Nothing is proved here.
