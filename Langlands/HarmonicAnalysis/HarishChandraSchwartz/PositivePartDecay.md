# Exponential decay of the positive part of a constant term (Waldspurger, Lemma VI.2.3, abstract form)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.PositivePartDecay`, namespace
`Langlands.HarishChandraSchwartz`. It imports `Langlands.HarmonicAnalysis.GroupAction` (for the
right translation representation `GroupAction.rightFunctions`, with
`rightFunctions g f x = f (x * g)`), `Mathlib.RingTheory.Polynomial.Vieta` (coefficients of
`∏ (X - z)` as elementary symmetric functions), `Mathlib.Analysis.Complex.Polynomial.Basic`
(`ℂ` is algebraically closed) and `Mathlib.Analysis.SpecialFunctions.Log.Basic`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. Overlines and calligraphic letters in the quotes below were checked on the
rendered PDF pages 8 and 64–67.

- Definitions before the lemma, printed p. 299 (PDF p. 65): "Si `P' = M'U'` est un sous-groupe
  parabolique standard de `G` et `δ` un réel `> 0`, on pose
  `D_{M'}(δ) = {m ∈ M̄_0^+; ∀α ∈ Δ_0 − Δ_0^{M'}, ⟨α, H_0(m)⟩ ⩾ δ|H_0(m)|}`. Pour tout
  `f ∈ 𝒜^w(G)`, on pose `f^+_{P'} = f_{P'} − f^w_{P'}`."
- Lemma VI.2.3, printed p. 299 (PDF p. 65): "Soient `P' = M'U'` un sous-groupe parabolique
  standard de `G`, `δ` un réel `> 0` et `ψ ∈ C^∞(𝒪, P)`. Alors il existe `ε > 0` et `C > 0`
  tels que, pour tous `ω ∈ 𝒪` et `m ∈ D_{M'}(δ)`, on ait l'inégalité
  `|(E^G_P ψ_ω)^+_{P'}(m)| ⩽ C Ξ^{M'}(m) e^{−ε|H_0(m)|}`."
- Its proof, printed pp. 299–301 (PDF pp. 65–67). After reducing to `sp_χ ψ` for
  `χ ∈ Im X(M)`, the proof first shows (1): "il existe `t > 0`, `C_1 > 0` et `d ∈ ℕ` tels que
  pour tout `χ ∈ Im X(M)` et tout `m ∈ M̄_0^+` tel que `⟨α, H_0(m)⟩ ⩾ t` pour tout
  `α ∈ Δ_0 − Δ_0^{M'}`, on ait l'inégalité
  `|(E^G_P sp_χ ψ)^+_{P'}(m)| ⩽ C_1 Ξ^{M'}(m)(1 + σ(m))^d`" (from I.5, Proposition I.4.3,
  Lemma VI.2.2, Lemma II.1.1 and the formula for the weak part from the proof of Lemma VI.2.1).
  Then, printed p. 300 (PDF p. 66): "`r_χ(X) = ∏_{ν ∈ 𝓔^+} (X − sp_χ ν(a))^{n(ν)}`.
  Développons ce polynôme: `r_χ(X) = Σ_{i=0}^N r_{i,χ} X^{N−i}`. Pour tout `ν ∈ 𝓔^+`,
  `|sp_χ ν(a)|` est indépendant de `χ` et appartient à l'intervalle `]0, 1[`. Quitte à remplacer
  `a` par une puissance convenable, on peut donc supposer que pour tout `i ∈ {1, ..., N}` et
  tout `χ ∈ Im X(M)`, `|r_{i,χ}| ⩽ 2^{−i}N^{−1}`." Estimate (2): "il existe `C_5 > 0` tel que
  pour tout `χ ∈ Im X(M)`, tout `n ∈ ℕ` et tout `m ∈ M̄_0^+` tel que `⟨α, H_0(m)⟩ ⩾ t` pour
  tout `α ∈ Δ_0 − Δ_0^{M'}`, on ait l'inégalité
  `|(E^G_P sp_χ ψ)^+_{P'}(a^n m)| ⩽ C_5 2^{−n} Ξ^{M'}(m)(1 + σ(m))^d`", with
  `C_5 = C_1 sup{2^n(1 + σ(a^n))^d; 0 ⩽ n ⩽ N − 1}`, proved by induction from "l'opérateur
  `(I^G_P(ω ⊗ χ))^+_{P'}(r_χ(a))` est nul donc `ρ(r_χ(a))` annule
  `(E^G_P sp_χ ψ)^+_{P'}`" and the recurrence
  `(E^G_P sp_χ ψ)^+_{P'}(a^n m) = −Σ_{i=1}^N r_{i,χ}(E^G_P sp_χ ψ)^+_{P'}(a^{n−i} m)`.
  Finally, printed p. 301 (PDF p. 67): "L'ensemble `{m ∈ D_{M'}(δ); |H_0(m)| ⩽ tδ^{−1}}` est
  compact. Pour tout `ε > 0`, on peut donc trouver `C > 0` tel que la majoration de l'énoncé
  soit vérifiée pour `m` dans cet ensemble." For `|H_0(m)| > tδ^{−1}`, `n` is "la plus petite
  des parties entières de `(δ|H_0(m)| − t)⟨α, H_0(a)⟩^{−1}` quand `α` parcourt
  `Δ_0 − Δ_0^{M'}`"; then `ma^{−n} ∈ M̄_0^+` with `⟨α, H_0(ma^{−n})⟩ ⩾ t`, "On a l'égalité
  `Ξ^{M'}(ma^{−n}) = Ξ^{M'}(m)`", "`1 + σ(ma^{−n}) ⩽ C_6(1 + |H_0(m)|)`, `r|H_0(m)| ⩽ n`", and
  "il existe `ε > 0` et `C_7 > 0` tels que pour tout `x ⩾ 0`, `2^{−rx}(1 + x)^d ⩽ C_7 e^{−εx}`".
- Proof of Lemma VI.2.1, printed p. 298 (PDF p. 64): the element `a` is fixed with
  "`a ∈ A_{M'}` tel que `|α(a)|_F < 1` pour tout `α ∈ Σ(P')`", and `|(sp_χ ν')(a)| < 1` for
  `ν' ∈ 𝓔^+` follows from Proposition III.2.2.
- I.1, printed p. 242 (PDF p. 8): "`‖g‖ ⩾ 1`, `‖g_1g_2‖ ⩽ ‖g_1‖‖g_2‖`", "`σ(g) = log‖g‖`", and
  for a `W^G`-invariant Euclidean norm on `a_0`, "Il existe `C_1, C_2 > 0` tels que pour tout
  `m ∈ M_0`, `C_1(1 + |H_0(m)|) ⩽ 1 + σ(m) ⩽ C_2(1 + |H_0(m)|)`. (6)"

The abstraction, the hypotheses and the proof route are internal to this project.

## Relation to the source

Dictionary for `exists_norm_le_exp_of_aeval_eq_zero`:

- `G` is `M_0` (the elements `m ∈ M̄_0^+` lie in `M_0`; the functions are restricted to `M_0`,
  which commutes with right translation by `a ∈ A_{M'} ⊂ M_0`), `E` is `a_0` with its norm,
  `H` is `H_0`, `S₀` is `Δ_0^{M'}` and `S` is `Δ_0 − Δ_0^{M'}`. The region
  `{β(H g) ≥ 0, β ∈ S₀; α(H g) ≥ δ‖H g‖, α ∈ S}` of the conclusion is `D_{M'}(δ)` (for
  `α ∈ S` the condition `⟨α, H_0(m)⟩ ⩾ 0` of `M̄_0^+` follows from `⟨α, H_0(m)⟩ ⩾ δ|H_0(m)|`),
  and the region `{β(H g) ≥ 0, β ∈ S₀; α(H g) ≥ t, α ∈ S}` of `h1` is the region of (1) when
  `t ≥ 0`.
- `ι` is `Im X(M)`, `F i` is `(E^G_P sp_χ ψ)^+_{P'}` restricted to `M_0`, `B` is `Ξ^{M'}`
  restricted to `M_0`, and `p i` is `r_χ`; `hann` is the sentence "`ρ(r_χ(a))` annule
  `(E^G_P sp_χ ψ)^+_{P'}`", with `ρ` the right translation `GroupAction.rightFunctions`.
- `h1` is estimate (1) and `h0` is the bound on the bounded part
  `{m ∈ D_{M'}(δ); |H_0(m)| ⩽ tδ^{−1}}`, which the source derives from compactness of that set.
- `θ < 1` bounds the moduli `|sp_χ ν(a)|` of the roots of `r_χ` uniformly in `χ`; the source
  states that they are independent of `χ` and lie in `]0, 1[`.

Obligations for an actual group, derived here and not formalized:

- `ha₀` and `ha`: `⟨β, H_0(a)⟩ = 0` for `β ∈ Δ_0^{M'}` (since `H_0(a) ∈ a_{M'}`) and
  `⟨α, H_0(a)⟩ > 0` for `α ∈ Δ_0 − Δ_0^{M'}` (these restrict on `a_{M'}` to elements of
  `Δ(P') ⊂ Σ(P')`, and `|α(a)|_F < 1` for `α ∈ Σ(P')`).
- `hσ0`, `hσ` and `hσH`: from the properties of `‖·‖` and from I.1 (6) quoted above.
- `hB0` and `hB`: `Ξ^{M'} ⩾ 0`, and `Ξ^{M'}(ma) = Ξ^{M'}(m)` for `a ∈ A_{M'}`, which the source
  uses in the form `Ξ^{M'}(ma^{−n}) = Ξ^{M'}(m)`.
- `hp`, `hpN`, `hroots`, `hann`, `h1`, `h0`: the facts about `r_χ` and the estimates quoted
  above; (1) depends on Proposition I.4.3, Lemmas VI.2.1, VI.2.2 and II.1.1, and `θ < 1` on
  Proposition III.2.2. None of these is derived in this module, and the objects `E^G_P`,
  `f^+_{P'}`, `𝓔^+` and `Im X(M)` do not occur in it.

Differences in the route. The source writes `a^n m`; since `a ∈ A_{M'}` is central in `M'`
this is `m a^n`, and the Lean statements use right translation throughout. The source takes
`n` to be the least of the integer parts of `(δ|H_0(m)| − t)⟨α, H_0(a)⟩^{−1}`; the Lean proof
uses `n = ⌊(δ‖H g‖ − t)/c⌋` with `c = Σ_{α ∈ S} α(H b) + 1`, which is at most each of these
quantities and still makes `⟨α, H_0(m b^{−n})⟩ ⩾ t`. The source's inequality `r|H_0(m)| ⩽ n`
fails when `|H_0(m)|` is close to `tδ^{−1}` (then `n` can be `0`); the Lean proof uses
`n > (δ‖H g‖ − t)/c − 1` instead, which only changes the constant.

## Contents

### Powers of the roots

- `rootPowerPolynomial p q : ℂ[X]` (definition): for `p : ℂ[X]` and `q : ℕ`, the product of
  `X - C (z ^ q)` over the multiset `p.roots` of roots of `p` counted with multiplicity.
- `rootPowerPolynomial_monic p q`: it is monic.
- `natDegree_rootPowerPolynomial p q`: its degree is `p.natDegree` (`ℂ` is algebraically
  closed).
- `dvd_rootPowerPolynomial_comp`: for monic `p` (`hp : p.Monic`) and `q : ℕ`,
  `p ∣ (rootPowerPolynomial p q).comp (X ^ q)`.
- `aeval_rootPowerPolynomial_eq_zero`: for a complex vector space `W`,
  `T : Module.End ℂ W`, monic `p` (`hp`), `q : ℕ` and `w : W` with `h : aeval T p w = 0`,
  `aeval (T ^ q) (rootPowerPolynomial p q) w = 0`. This is "Quitte à remplacer `a` par une
  puissance convenable" for the annihilating polynomial.
- `norm_multiset_prod_le_pow`: for a multiset `t` of complex numbers and `η` with `hη0 : 0 ≤ η`
  and `hη : ∀ z ∈ t, ‖z‖ ≤ η`, `‖t.prod‖ ≤ η ^ card t`.
- `norm_esymm_le`: for a multiset `s` of complex numbers, `hη0 : 0 ≤ η`,
  `hη : ∀ z ∈ s, ‖z‖ ≤ η` and `j : ℕ`, `‖s.esymm j‖ ≤ 2 ^ card s * η ^ j`.
- `norm_coeff_rootPowerPolynomial_le`: for `p : ℂ[X]`, `θ` with `hθ0 : 0 ≤ θ` and
  `hθ : ∀ z ∈ p.roots, ‖z‖ ≤ θ`, `q : ℕ` and `k` with `hk : k ≤ p.natDegree`,
  `‖(rootPowerPolynomial p q).coeff k‖ ≤ 2 ^ p.natDegree * (θ ^ q) ^ (p.natDegree - k)`.
- `exists_pow_coeff_small`: for `N : ℕ` and `θ` with `hθ0 : 0 ≤ θ`, `hθ : θ < 1`, there is
  `q ≥ 1` with `2 ^ N * (θ ^ q) ^ i ≤ (1 / 2) ^ i / N` for all `1 ≤ i ≤ N`. With the previous
  lemma (`i = N − k`) this gives the source's `|r_{i,χ}| ⩽ 2^{−i}N^{−1}`.

### Decay along powers

- `norm_le_of_linearRecurrence`: for `f : ℕ → ℂ`, `N : ℕ`, `c : ℕ → ℂ` with
  `hrec : ∀ n, f (n + N) = -∑ k ∈ Finset.range N, c k * f (n + k)`,
  `hc : ∀ k < N, ‖c k‖ ≤ (1 / 2) ^ (N - k) / N`, `K` with `hK : 0 ≤ K` and
  `h0 : ∀ n < N, ‖f n‖ ≤ K * (1 / 2) ^ n`: `‖f n‖ ≤ K * (1 / 2) ^ n` for every `n`.
- `eq_neg_sum_of_aeval_eq_zero`: for a group `G`, `b : G`, monic `p` (`hp`), `F : G → ℂ` with
  `h : aeval (GroupAction.rightFunctions b) p F = 0`, `m : G` and `n : ℕ`,
  `F (m * b ^ (n + p.natDegree)) = -∑ k ∈ Finset.range p.natDegree,
  p.coeff k * F (m * b ^ (n + k))`.
- `norm_le_of_aeval_eq_zero` (estimate (2), abstract): for `b : G`, monic `p` (`hp`),
  `hc : ∀ k < p.natDegree, ‖p.coeff k‖ ≤ (1 / 2) ^ (p.natDegree - k) / p.natDegree`,
  `F` with `h` as above, `m : G`, `K` with `hK : 0 ≤ K` and
  `h0 : ∀ n < p.natDegree, ‖F (m * b ^ n)‖ ≤ K * (1 / 2) ^ n`: for every `n`,
  `‖F (m * b ^ n)‖ ≤ K * (1 / 2) ^ n`.

### Auxiliary bounds (derived)

- `one_add_pow_le_mul_exp`: for `hs : 0 < s`, `hx : 0 ≤ x` and `d : ℕ`,
  `(1 + x) ^ d ≤ (1 + 1 / s) ^ d * Real.exp (d * (s * x))`.
- `one_half_pow_eq_exp n`: `(1 / 2 : ℝ) ^ n = Real.exp (-(n * Real.log 2))`.
- `map_pow_of_additive`: for `H : G → E` (`E` a real normed space) with
  `hH : ∀ x y, H (x * y) = H x + H y`, `H (g ^ n) = (n : ℝ) • H g`.

### The abstract Lemma VI.2.3

`exists_norm_le_exp_of_aeval_eq_zero`. Context: a group `G`, a real seminormed space `E`
(`[SeminormedAddCommGroup E]`, `[NormedSpace ℝ E]`). Hypotheses:

- `H : G → E` with `hH : ∀ x y, H (x * y) = H x + H y`;
- finite sets `S₀ S : Finset (Module.Dual ℝ E)` and `a : G` with
  `ha₀ : ∀ β ∈ S₀, β (H a) = 0` and `ha : ∀ α ∈ S, 0 < α (H a)`;
- `σ : G → ℝ` with `hσ0 : ∀ g, 0 ≤ σ g`, `hσ : ∀ g h, σ (g * h) ≤ σ g + σ h` and
  `hσH : ∃ C : ℝ, ∀ g, 1 + σ g ≤ C * (1 + ‖H g‖)`;
- `B : G → ℝ` with `hB0 : ∀ g, 0 ≤ B g` and `hB : ∀ g, B (g * a) = B g`;
- a type `ι`, `F : ι → G → ℂ`, `p : ι → ℂ[X]`, `N : ℕ` and `θ` with `hθ : θ < 1`,
  `hp : ∀ i, (p i).Monic`, `hpN : ∀ i, (p i).natDegree = N`,
  `hroots : ∀ i, ∀ z ∈ (p i).roots, ‖z‖ ≤ θ` and
  `hann : ∀ i, aeval (GroupAction.rightFunctions a) (p i) (F i) = 0`;
- `t` with `ht : 0 ≤ t`, `C₁ : ℝ`, `d : ℕ` and
  `h1 : ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, t ≤ α (H g)) →
  ‖F i g‖ ≤ C₁ * B g * (1 + σ g) ^ d`;
- `δ` with `hδ : 0 < δ`, `C₀ : ℝ` and
  `h0 : ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, δ * ‖H g‖ ≤ α (H g)) →
  ‖H g‖ ≤ t / δ → ‖F i g‖ ≤ C₀ * B g`.

Conclusion: `∃ ε > 0, ∃ C : ℝ, ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) →
(∀ α ∈ S, δ * ‖H g‖ ≤ α (H g)) → ‖F i g‖ ≤ C * B g * Real.exp (-(ε * ‖H g‖))`, i.e.
`|F_χ(m)| ⩽ C Ξ^{M'}(m) e^{−ε|H_0(m)|}` on `D_{M'}(δ)`, uniformly in `χ`, under the
dictionary above.

## Proof

`dvd_rootPowerPolynomial_comp`: `p = ∏_{z ∈ roots} (X − z)` because `p` is monic and splits
over `ℂ`, and `(rootPowerPolynomial p q).comp (X^q) = ∏_z (X^q − z^q)`; each `X − z` divides
`X^q − z^q`. `aeval_rootPowerPolynomial_eq_zero` follows: `aeval (T^q) r = aeval T (r.comp X^q)`
and `r.comp X^q = p s`. `norm_coeff_rootPowerPolynomial_le` writes the coefficient of `X^k` as
`± e_{N−k}` of the `q`-th powers of the roots (`Multiset.prod_X_sub_C_coeff`) and bounds
`e_j` by `card(powersetCard j) η^j ≤ 2^N η^j` (`norm_esymm_le`). `exists_pow_coeff_small`
takes `q` with `θ^q < 1/(2^{N+1} N)`; then `η = θ^q` satisfies `2η ≤ 1` and
`2^N η^i = 2^N (2η)^i 2^{−i} ≤ 2^N (2η) 2^{−i} ≤ 2^{−i}/N`.

`norm_le_of_linearRecurrence`: if `N = 0` the recurrence makes every `f n` zero. Otherwise by
strong induction, for `n = m + N`,
`‖f n‖ ≤ Σ_{k<N} 2^{−(N−k)}/N · K 2^{−(m+k)} = K 2^{−n}`.
`eq_neg_sum_of_aeval_eq_zero` evaluates `aeval ρ(b) p F = Σ_k c_k ρ(b)^k F` at `m bⁿ`, using
`ρ(b)^k = ρ(b^k)` and `c_N = 1`; `norm_le_of_aeval_eq_zero` combines the two.

`exists_norm_le_exp_of_aeval_eq_zero`. Put `θ' = max θ 0`, choose `q` by
`exists_pow_coeff_small` and set `b = a^q`. The polynomials `rootPowerPolynomial (p i) q` are
monic of degree `N`, kill `F i` under `ρ(b) = ρ(a)^q`, and have the small coefficients needed
by `norm_le_of_aeval_eq_zero`. Also `β(H b) = 0` on `S₀`, `α(H b) > 0` on `S`, and
`B(g bⁿ) = B(g)`.

Estimate (2): for `g` in the region of `h1` and every `n`,
`‖F i (g bⁿ)‖ ≤ C₅ B(g) (1 + σ(g))^d 2^{−n}` with
`C₅ = |C₁| Σ_{k<N} 2^k (1 + σ(b^k))^d`. For `n < N` this is `h1` at `g bⁿ` (which stays in the
region) with `1 + σ(g bⁿ) ≤ (1 + σ(g))(1 + σ(bⁿ))`; for all `n` it is
`norm_le_of_aeval_eq_zero`.

For `g` in `D(δ)` with `‖H g‖ ≤ t/δ`, `h0` gives `‖F i g‖ ≤ |C₀| e^{ε t/δ} B(g) e^{−ε‖H g‖}`.
Otherwise let `x = ‖H g‖`, `c = Σ_{α ∈ S} α(H b) + 1`, `n = ⌊(δx − t)/c⌋` and
`g' = g b^{−n}`. Then `β(H g') = β(H g) ≥ 0` for `β ∈ S₀` and
`α(H g') = α(H g) − n α(H b) ≥ δx − nc ≥ t` for `α ∈ S`, so estimate (2) applies to `g'` and
`n`: `‖F i g‖ ≤ C₅ B(g) (1 + σ(g'))^d 2^{−n}`. Since `n ≤ δx/c`,
`‖H g'‖ ≤ x + n‖H b‖` gives `1 + σ(g') ≤ C₆(1 + x)` with
`C₆ = |C|(1 + δ‖H b‖/c)`, `C` the constant of `hσH`. Since `n > (δx − t)/c − 1`,
`2^{−n} ≤ e^{(t/c + 1) log 2} e^{−r x}` with `r = δ log 2 / c`. Finally
`(1 + x)^d ≤ (1 + 1/s)^d e^{d s x}` with `s = ε/(d + 1)` and `ε = r/2`, so
`e^{d s x} e^{−r x} ≤ e^{−ε x}`. The constant is the larger of the two cases.
