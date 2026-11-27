# Approximation of the constant term of Eisenstein series by the weak constant term on cones

Module `Langlands.Global.AdelicEisensteinConstantTermWeakApproximationStatement`, namespace
`Langlands.Global`. It states one proposition, `EisensteinConstantTermWeakApproximationStatement`,
and proves nothing.

## Source

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF numbering).

- §3.1, pp.9–10: the exponents (3.2) are normalized. An element of `A^n_P(G)` satisfies
  `φ(exp X g) = e^{ρ_P(X)} φ(g)` for `X ∈ 𝔞_P`, and `φ = ∑_{λ ∈ 𝓔_P(φ)} e^{λ(H_P(·))} φ_{0,λ}` with
  `φ_{0,λ} ∈ S(𝔞_P^*) ⊗ A^n_P(G)`. So `X ↦ e^{−ρ_P(X)} φ(exp X g)`, and not `φ(exp X g)` itself,
  has the exponents `𝓔_P(φ)`.
- §4.1, pp.16–17: the relative Eisenstein series (4.1), the weak constant term (4.3)
  `E_P(·, φ, λ)^w_Q = ∑_{s ∈ W(P, Q)} E^Q_{Q_s}(·, M(s, λ) φ, s λ)`, holomorphic in a neighborhood
  of `i𝔞_P^*`, and (4.4). For `λ ∈ i𝔞_P^*` and `E^-_Q = E_Q − E^w_Q`, the function
  `X ↦ E_P(exp X g, φ, λ)^-_Q` on `𝔞_Q` is an exponential polynomial in the normalized sense of
  (3.2): after division by `e^{ρ_Q(X)}` its exponents lie in a finite list `𝓔̃^-_Q(λ)` with
  repetitions, built from
  `𝓔^-_Q(λ) = ∪_{s ∈ W(Q\G/P) \ W(P, Q)} {s(𝓔_{P_s}(φ) + λ)|_{𝔞_Q}}`, with multiplicities
  depending on those of the exponents of `φ`. Their real parts do not depend on `λ ∈ i𝔞_P^*`.
- §4.2, p.17: Proposition 4.1 (uniform temperedness).
- §5.1, pp.18–19, proof of Lemma 5.1. Take `X ∈ 𝔞_0^+`, `Y` in the compact set `S_{Q,δ}` of unit
  vectors of `𝔞^{G,+}_{Q,δ} = {Y ∈ 𝔞_Q^{G,+} : α(Y) ≥ δ‖Y‖, α ∈ Δ_Q}`, and `ω ∈ Ω`. The
  exponential polynomials `p_{Y,X,ω}(t) = (φ_Q − φ^w_Q)(exp X exp tY ω)` satisfy the polynomial
  bound (5.1). Their exponents are `μ(Y) + ρ(Y)`, where `μ` runs over the normalized exponents
  of `φ_Q` that are not imaginary, and there is `ε' > 0` with `Re μ(Y) < −ε'` for
  `Y ∈ S_{Q,δ}`. So the normalized functions `e^{−tρ(Y)} p_{Y,X,ω}(t)` have exponents
  `μ(Y)` of strictly negative real part. Lapid's Lemma 3 applies to these functions, divided by
  `(1 + ‖X‖)^d e^{ρ(X)}`. Reinserting `e^{tρ(Y)}` gives
  `|(φ_Q − φ^w_Q)(n_Q exp X exp Y ω)| ≪ (1 + ‖X‖)^d e^{ρ(X)} e^{ρ(Y) − ε‖Y‖}` for
  `Y ∈ 𝔞^{G,+}_{Q,δ}`. Lemma 5.2, p.19: the passage to the cone
  `𝔞^{G+}_{0,Q,δ} = {X ∈ 𝔞_0^{G+} : α(X) ≥ δ‖X‖, α ∈ Δ_{P_0} \ Δ^Q_{P_0}}`. Lemma 5.3,
  pp.19–20: the analogue for Eisenstein series, using Proposition 4.1, the independence of the
  real parts of the exponents of `E_P(·, φ, λ)_Q` from `λ ∈ i𝔞_P^*`, and (4.3).

E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series* (Clay
Math. Proc. 13, 2011), registered as `lapid-2011-asymptotic-inner-product-truncated-eisenstein`:

- printed pp.315–316: for an exponential polynomial `f = ∑_i e^{⟨λ_i, ·⟩} P_i`, the multiset
  `𝓔(f)` contains each `λ_i` exactly `deg P_i + 1` times, and `PE^V_{≤l}(A)` is the set of `f`
  for which `𝓔(f)` has at most `l` elements, all in `A`. Lemma 1 (p.316): for compact `A`, a
  sequence in `PE^V_{≤l}(A)` that converges pointwise on a nonempty open set converges
  everywhere, and its limit lies in `PE^V_{≤l}(A)`.
- Lemma 3, printed p.317. Let `A` be a compact set of exponents negative with respect to a cone
  `C`. There is `δ_A > 0` (written `δ` in the source), depending only on `Re A`, with the
  following property. Let `l ≥ 1` and let `F ⊆ PE^V_{≤l}(A)` be a family bounded on a
  neighborhood of `u`. Then `sup_{f ∈ F} sup_{v ∈ u + C} |f(v)| e^{δ_A‖v‖} < ∞`. The hypothesis
  bounds the whole multiset
  of each `f`, that is the sum over its exponents of one plus the degree of the coefficient; a
  bound on the degrees of the coefficients alone is not enough.
- (12), (13), Lemma 6 and Corollary 2, printed pp.322–323. Lapid writes the constant term of
  `E_P(φ, λ)` along `Q` as `M_Q + E_Q`, where `M_Q` is the sum over `w ∈ Ω(P; Q)`. So `M_Q` is
  Delorme's weak constant term (4.3), and Lapid's `E_Q` is Delorme's `E^-_Q`. (13) lists its
  exponents, and Lemma 6 shows they are subunitary and not unitary. Corollary 2 gives a constant
  `κ` (written `k` in the source) with the following property. For every `λ` outside the
  singular hyperplanes of the Eisenstein series and the intertwining operators, and every
  `R ⊆ Q`, the union of the exponent multisets of `M_Q` and `E_Q` along `R` has at most `κ`
  elements and lies in a ball of radius `‖λ‖ + κ`. The real parts of these exponents, over all
  `λ ∈ i𝔞_P^*`, form finite sets, and the set for `E_Q` does not contain `0`.

## The statement

The data are exactly those of `EisensteinWeakConstantTermApproximationStatement`
(`Langlands/Global/AdelicEisensteinWeakConstantTermApproximationStatement.md`, "The
statement"), including `hKQ : IsIwasawaCompact (Standard.parabolicHom i ν J) K` with its height
power `m_Q(g)^λ = hKQ.heightPower λ g`, and `δ > 0`, a threshold `t` and a compact `Ω`.

Let `N_Q → G` be `Standard.unipotentHom i ν J`, the unipotent radical of `Q = Q_J`, and write
`E(i e(x))_Q(g) = subgroupConstantTerm F (Standard.unipotentHom i ν J) (E (i e(x))) g` for the
constant term `∫_{N_Q(F) \ N_Q(𝔸)} E(i e(x))(u g) du` (quotient Haar measure of total mass one).

Conclusion: there are `ε > 0`, `m : ℕ`, `B`, `k : ℕ` and for each `q < k` a function
`c_q : ℝⁿ → ℂ`, a real subspace `V_q ⊆ ℝⁿ`, a real linear map
`L_q : V_q → X^*(Q) ⊗ ℝ` and a function `Φ_q : ℝⁿ → G(𝔸) → ℂ`, such that items 1–6 of
`EisensteinWeakConstantTermApproximationStatement` hold (`ε > 0`, smooth `c_q`, surjective
`L_q`, the shift law `Φ_q(x + v, g) = m_Q(g)^{i L_q(v)} Φ_q(x, g)` for `v ∈ V_q`, continuity of
`x ↦ Φ_q(x, g)`, and `‖Φ_q(x, z b ω)‖ ≤ B · δ(b)^{1/2} · σ(z b ω)^m`), and

7'. `‖E(i e(x))_Q(z b ω) − ∑_q c_q(x) Φ_q(x, z b ω)‖ ≤ B · δ(b)^{1/2} · e^{−ε R}` for `x ∈ C`,
`z ∈ A_G`, `b` in the weak simple-root chamber `|β(b)| ≥ t`, `ω ∈ Ω` and every real `R` with
`|log |β(b)|| ≤ R` for all `β ∈ Δ` and `δ R ≤ log |α(b)|` for all `α ∈ Δ \ J`.

Only item 7' differs from item 7 of `EisensteinWeakConstantTermApproximationStatement`: the
constant term `E_Q` replaces `E`.

## Correspondence with the source

Take first `P` standard and `K` in good position, as in Delorme.

- **Items 1–6.** In Delorme's setting the weak constant term (4.3) supplies the triples, exactly
  as described in `AdelicEisensteinWeakConstantTermApproximationStatement.md` ("Correspondence
  with the source": the functions `Φ_q` and `c_q`, item 4 and item 6): `Φ_q(x, g)` is the relative
  Eisenstein series `E^Q_{Q_s}(g, ψ_{s,l}, s i e(x))` of a basis vector `ψ_{s,l}` of the
  finite-dimensional space containing the `M(s, λ) φ`, and `c_q(x)` is the coefficient of
  `M(s, i e(x)) φ` along `ψ_{s,l}`; item 6 is Proposition 4.1 for `M_Q` transported by (4.1).
  Then `∑_q c_q(x) Φ_q(x, ·) = E_P(·, φ, i e(x))^w_Q`.
- **Item 7'.** The left side is `|E^-_Q(z b ω)|` with `E^-_Q = E_Q − E^w_Q`. This is the bound
  for `φ_Q − φ^w_Q` in the proof of Lemma 5.1, carried out for `E_Q` as in Lemma 5.3, followed by
  Lemma 5.2:
  - **Exponents.** Fix `X ∈ 𝔞_0^+`, `Y ∈ S_{Q,δ}`, `ω ∈ Ω` and `λ ∈ i e(C)`. By (4.4), the
    normalized function `f(t) = e^{−tρ(Y)} E^-_Q(exp X exp tY ω)` is an exponential polynomial
    with exponents `μ(Y)`, where `μ` runs over `𝓔̃^-_Q(λ)`. The function
    `t ↦ E^-_Q(exp X exp tY ω)` itself has the exponents `μ(Y) + ρ(Y)`. The real parts of the
    `μ` do not depend on `λ ∈ i𝔞_P^*` and form a finite set. They are subunitary and not unitary
    (Lapid, (13) and Lemma 6), so `Re μ(Y) < −ε'` for `Y ∈ S_{Q,δ}`. The imaginary parts stay
    in a compact set because `λ` does. So all exponents `μ(Y)` lie in one compact set `A` of
    exponents that are negative with respect to the ray `[0, ∞)`.
  - **Multiplicities.** Lapid's Lemma 3 also needs a uniform bound on the size of the exponent
    multisets (each exponent counted one plus the degree of its coefficient). The finite lists
    with repetitions of (4.4) and Lapid's Corollary 2 bound the exponent multiset of
    `X' ↦ e^{−ρ_Q(X')} E^-_Q(exp X' g)` on `𝔞_Q` by the constant `κ`, for every `λ` outside the
    singular hyperplanes. Restriction to the line `X + tY` does not increase the size: exponents
    that become equal on the line combine, and the combined coefficient has degree at most the
    largest degree among the coefficients combined. Corollary 2 excludes the singular
    hyperplanes. At an imaginary parameter on such a hyperplane, individual terms of (4.2) may be
    singular and their exponents may collide, but `E^-_Q` is still holomorphic (Delorme, p.17),
    so it is the pointwise limit of its values at nearby regular parameters. Corollary 2 places
    their exponents in a fixed closed ball, and Lapid's Lemma 1 then keeps the bound `κ` in the
    limit. So every `f` lies in `PE^ℝ_{≤κ}(A)`, uniformly in `X`, `Y`, `ω` and `x ∈ C`.
  - **Bound near the origin of the ray.** The polynomial bound (5.1) for `E^-_Q` holds
    uniformly in `λ ∈ i e(C)`. For `E_Q` it follows from Proposition 4.1 and the bound for
    `E − E_Q` given by Lemma 3.1 (the statement `EisensteinConstantTermDecayStatement`). For
    `E^w_Q` it follows from item 6. Applied to a compact
    `Ω' ⊇ {exp tY : |t| ≤ ε'', Y ∈ S_{Q,δ}} Ω`, it bounds `[(1 + ‖X‖)^d e^{ρ(X)}]^{-1} f` on
    `[−ε'', ε'']` uniformly.
  - **Lapid's Lemma 3.** The lemma, applied to the family of these functions, gives
    `|f(t)| ≪ (1 + ‖X‖)^d e^{ρ(X)} e^{−εt}` for `t ≥ 0`. Reinserting `e^{tρ(Y)}` gives
    `|E^-_Q(exp X exp Y ω)| ≪ (1 + ‖X‖)^d e^{ρ(X)} e^{ρ(Y) − ε‖Y‖}` for `X ∈ 𝔞_0^+`,
    `Y ∈ 𝔞^{G,+}_{Q,δ}` and `ω ∈ Ω`, uniformly in `x ∈ C`. Left `N_Q(𝔸)`-invariance of `E_Q`
    and of `E^w_Q` removes `n_Q`.
  - Lemma 5.2: for `X = H_0(b)` in the cone, let `Y ∈ 𝔞_Q^G` with `α(Y) = α(X)` for
    `α ∈ Δ \ J`; then `X − Y` lies in the closed positive chamber, `‖X − Y‖ ≪ ‖X‖` and
    `Y ∈ 𝔞^{G,+}_{Q,δ_1}` for a fixed `δ_1 > 0`. Hence
    `|E^-_Q(b ω)| ≪ e^{ρ(X) − ε‖X‖}`. The translation of the cone `𝔞^{G+}_{0,Q,δ}` and of
    `e^{−ε‖X‖}` into the conditions on `R` of item 7', the treatment of a threshold `t < 1` and
    the passage from `ρ(X)` to `δ(b)^{1/2}` are those described for item 7 in
    `AdelicEisensteinWeakConstantTermApproximationStatement.md`.
  - `z ∈ A_G` is central; `E_Q` and every term of `E^w_Q` transform under `A_G` by the same
    unitary character `e^{λ(H_G(z))}` (each `s ∈ W(P, Q)` fixes `𝔞_G`), so the left side of
    item 7' does not depend on `z`.
- **The constant term.** `Standard.unipotentHom i ν J` is the composite of the unipotent radical
  `Standard.unipotentToParabolic i ν J` of the standard parabolic datum
  (`ParabolicDatum.standard`) with `Standard.parabolicHom i ν J`
  (`Standard.unipotentToParabolic_comp`), so `E_Q` is Delorme's constant term along `Q`.
- **Continuations and transfers.** As in
  `AdelicEisensteinWeakConstantTermApproximationStatement.md` ("Continuations", "Transfers").

## Scope

The statement does not assert the formula (4.3), the description (4.4) of the exponents, the
holomorphy of `M(s, λ)` or Lapid's Lemma 3; it asserts the existence of a decomposition with items
1–6 and 7'. It does not identify `∑_q c_q Φ_q` with the weak constant term. For empty `Ω` the
bounds of items 6 and 7' are vacuous. `K` is assumed Iwasawa for the minimal parabolic of the
setup and for `Q`. Together with `EisensteinConstantTermDecayStatement` it implies
`EisensteinWeakConstantTermApproximationStatement`
(`Langlands/Global/AdelicEisensteinWeakConstantTermApproximationReduction.lean`). Nothing is
proved here.
