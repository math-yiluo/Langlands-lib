# The weak part as a bounded combination of translates (Waldspurger, proofs of Lemmas VI.2.1 (ii) and VI.2.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakPartProjection`, namespace
`Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.PositivePartDecay` (for `norm_esymm_le`,
`map_pow_of_additive` and the abstract Lemma VI.2.3 `exists_norm_le_exp_of_aeval_eq_zero`;
through it `GroupAction.rightFunctions`, the right translation `ρ`, and Mathlib's polynomial
library).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. Overlines and calligraphic letters in the quotes below were checked on the
rendered PDF pages 64–66.

- Proof of Lemma VI.2.1 (ii), printed p. 298 (PDF p. 64): for "`a ∈ A_{M'}` tel que
  `|α(a)|_F < 1` pour tout `α ∈ Σ(P')`", "La théorie du résultant entraîne l'existence de
  polynômes `Q(X), R(X) ∈ B[X]` tels que
  `Q(X) ∏_{ν ∈ 𝓔^w} (X − ν(a))^{n(ν)} + R(X) ∏_{ν ∈ 𝓔^+} (X − ν(a))^{n(ν)} = b`, où
  `b = ∏_{ν ∈ 𝓔^w} ∏_{ν' ∈ 𝓔^+} (ν(a) − ν'(a))^{n(ν)n(ν')}`. Posons
  `S = R(a) ∏_{ν ∈ 𝓔^+} (a − ν(a))^{n(ν)}`." Then: "si `ν ∈ 𝓔^w`, `Re(sp_χ ν) = 0` donc
  `|(sp_χ ν)(a)| = 1`. Tandis que si `ν' ∈ 𝓔^+`, `Re(sp_χ ν') ∈ +ā^{G*}_{P'}` d'après la
  Proposition III.2.2 et `Re(sp_χ ν') ≠ 0` d'après la définition de `𝓔^+`, donc
  `|(sp_χ ν')(a)| < 1`." and "L'opérateur `b(χ)^{−1} π_{χ,P'}(sp_χ S)` est donc rationnel et
  régulier sur `Im X(M)`, il annule `V^+_{χ,P'}` et agit par l'identité sur `V^w_{χ,P'}`. On a
  alors l'égalité `(E^G_P sp_χ ψ)^w_{P'} = b(χ)^{−1} ρ(sp_χ S)(E^G_P sp_χ ψ)_{P'}`."
- Proof of Lemma VI.2.3, printed p. 300 (PDF p. 66): "il existe un élément
  `a ∈ A_{M'} ∩ M̄_0^+`, un entier `n` et, pour tout `i ∈ {0, ..., n}`, une fonction rationnelle
  `b_i`, régulière sur `Im X(M)`, de sorte que pour tous `χ ∈ Im X(M)`, `m' ∈ M'`, on ait
  l'égalité `(E^G_P sp_χ ψ)^w_{P'}(m') = Σ_{i=0}^n b_i(χ)(E^G_P sp_χ ψ)_{P'}(a^i m')`. Les
  fonctions `b_i` sont bornées d'après la compacité de l'ensemble `Im X(M)`. De la majoration
  déjà démontrée de `(E^G_P sp_χ ψ)_{P'}(m)`, on déduit alors une majoration analogue pour
  `(E^G_P sp_χ ψ)^w_{P'}(m')` puis, par différence, la majoration (1)." Estimate (1) and the
  rest of the proof are quoted in `PositivePartDecay.md`; printed p. 299 (PDF p. 65) defines
  `f^+_{P'} = f_{P'} − f^w_{P'}`.

The abstraction, the hypotheses and the proof route are internal to this project.

## Relation to the source

- `F i`, `Fw i`, `Fp i` are `(E^G_P sp_χ ψ)_{P'}`, `(E^G_P sp_χ ψ)^w_{P'}` and
  `(E^G_P sp_χ ψ)^+_{P'}` (restricted to `M_0` as in `PositivePartDecay.md`), indexed by
  `χ ∈ Im X(M)`; `F = F^w + F^+` is the definition `f^+_{P'} = f_{P'} − f^w_{P'}`.
- `pw i` and `pp i` are `∏_{ν ∈ 𝓔^w} (X − sp_χ ν(a))^{n(ν)}` and
  `r_χ = ∏_{ν ∈ 𝓔^+} (X − sp_χ ν(a))^{n(ν)}`. The hypotheses that they annihilate `F^w` and `F^+`
  under `ρ(a)` encode that the weak and positive parts are coefficients of `V^w_{χ,P'}` and
  `V^+_{χ,P'}`, on which these operators vanish; the root conditions are the quoted
  `|(sp_χ ν)(a)| = 1` and `|(sp_χ ν')(a)| < 1`, the latter uniformly in `χ` (the source states
  that these moduli are independent of `χ`). None of this is derived here.
- The source writes `a^i m'`; `a` is central in `M'`, so this is `m' a^i`, and the module uses
  right translation.

Differences in the route. The source obtains the projection `b(χ)^{−1} ρ(sp_χ S)` from the
resultant and bounds its coefficients `b_i(χ)` by regularity on the compact `Im X(M)`. The Lean
proof builds the projection polynomial directly: `X − w` is inverted modulo `p_w` by
`−p_w(w)^{−1} (p_w /ₘ (X − w))` for each root `w` of `p_+`, and the coefficient bounds come
from `|p_w(w)| ≥ (1 − θ)^{N_w}`. This gives explicit bounds depending only on `N_w`, `N_+` and
`θ`, so no compactness or regularity in `χ` is used.

## Contents

### Coefficient bounds

- `IsCoeffBounded f d B` (definition), for `f : ℂ[X]`, `d : ℕ`, `B : ℝ`: `f.natDegree ≤ d` and
  `‖f.coeff k‖ ≤ B` for every `k`.
- `isCoeffBounded_one`: `IsCoeffBounded 1 0 1`.
- `sum_range_norm_coeff_le`: if `hg : g.natDegree ≤ d`, then for every `m`,
  `∑ j ∈ Finset.range m, ‖g.coeff j‖ ≤ ∑ j ∈ Finset.range (d + 1), ‖g.coeff j‖`.
- `IsCoeffBounded.mul`: from `IsCoeffBounded f d₁ B₁` and `IsCoeffBounded g d₂ B₂`,
  `IsCoeffBounded (f * g) (d₁ + d₂) ((d₂ + 1) * B₁ * B₂)`.
- `isCoeffBounded_multiset_prod`: if every element of a multiset `s` of polynomials satisfies
  `IsCoeffBounded x d B`, then
  `IsCoeffBounded s.prod (card s * d) (((d + 1) * B) ^ card s)`.
- `isCoeffBounded_of_roots`: for monic `p` (`hp`) and `Λ` with `hΛ : 1 ≤ Λ` and
  `hroots : ∀ z ∈ p.roots, ‖z‖ ≤ Λ`,
  `IsCoeffBounded p p.natDegree (2 ^ p.natDegree * Λ ^ p.natDegree)`.
- `pow_le_norm_multiset_prod`: for a multiset `t` of complex numbers, `hη0 : 0 ≤ η` and
  `hη : ∀ z ∈ t, η ≤ ‖z‖`, `η ^ card t ≤ ‖t.prod‖`.
- `pow_le_norm_eval`: for monic `p` (`hp`) with `hroots : ∀ z ∈ p.roots, ‖z‖ = 1`, `θ` with
  `hθ : θ < 1` and `w` with `hw : ‖w‖ ≤ θ`, `(1 - θ) ^ p.natDegree ≤ ‖p.eval w‖`.

### The projection polynomial

- `invXSubCMod p w` (definition): `C (-(p.eval w)⁻¹) * (p /ₘ (X - C w))`.
- `dvd_X_sub_C_mul_invXSubCMod_sub_one`: if `hw : p.eval w ≠ 0`, then
  `p ∣ (X - C w) * invXSubCMod p w - 1`.
- `isCoeffBounded_invXSubCMod`: for monic `p` (`hp`) with roots of modulus `1` (`hroots`), `θ`
  with `hθ : θ < 1` and `‖w‖ ≤ θ` (`hw`), `IsCoeffBounded (invXSubCMod p w) (p.natDegree - 1)
  (((1 - θ) ^ p.natDegree)⁻¹ * (p.natDegree * 2 ^ p.natDegree))`.
- `dvd_multiset_prod_sub_one`: if `p ∣ x - 1` for every `x` in a multiset `s`, then
  `p ∣ s.prod - 1`.
- `exists_projection_polynomial`: for `Nw Np : ℕ` and `θ` with `hθ : θ < 1` there is `C` such
  that for all `pw pp : ℂ[X]` that are monic with `pw.natDegree = Nw`, `pp.natDegree = Np`,
  `∀ z ∈ pw.roots, ‖z‖ = 1` and `∀ z ∈ pp.roots, ‖z‖ ≤ θ`, there is `E` with
  `IsCoeffBounded E (Np * (Nw - 1) + Np) C`, `pw ∣ E - 1` and `pp ∣ E`.
- `aeval_apply_eq_of_dvd`: for a complex vector space `W`, `T : Module.End ℂ W`,
  `h1 : pw ∣ E - 1`, `h2 : pp ∣ E`, and `x = xw + xp` (`hx`) with `hw : aeval T pw xw = 0` and
  `hp : aeval T pp xp = 0`: `aeval T E x = xw`. This is "il annule `V^+_{χ,P'}` et agit par
  l'identité sur `V^w_{χ,P'}`" for `E(T)`.
- `exists_norm_le_sum_translates`: for a group `G`, `a : G`, `Nw Np : ℕ` and `hθ : θ < 1` there
  is `C` such that for all `pw pp` as in `exists_projection_polynomial` and all
  `F Fw Fp : G → ℂ` with `F = Fw + Fp`, `aeval (GroupAction.rightFunctions a) pw Fw = 0` and
  `aeval (GroupAction.rightFunctions a) pp Fp = 0`, for every `m`,
  `‖Fw m‖ ≤ C * ∑ i ∈ Finset.range (Np * (Nw - 1) + Np + 1), ‖F (m * a ^ i)‖`. This is the
  formula `(E^G_P sp_χ ψ)^w_{P'}(m') = Σ_i b_i(χ)(E^G_P sp_χ ψ)_{P'}(a^i m')` with bounded
  `b_i`, in the form of an inequality.

### Lemma VI.2.3 from the bound on the constant term

`exists_norm_le_exp_of_decomposition`. Context: a group `G` and a real seminormed space `E`.
Hypotheses:

- `H : G → E` with `hH : ∀ x y, H (x * y) = H x + H y`; `S₀ S : Finset (Module.Dual ℝ E)`;
  `a : G` with `ha₀ : ∀ β ∈ S₀, β (H a) = 0` and `ha : ∀ α ∈ S, 0 < α (H a)`;
- `σ : G → ℝ` with `hσ0 : ∀ g, 0 ≤ σ g`, `hσ : ∀ g h, σ (g * h) ≤ σ g + σ h` and
  `hσH : ∃ C : ℝ, ∀ g, 1 + σ g ≤ C * (1 + ‖H g‖)`;
- `B : G → ℝ` with `hB0 : ∀ g, 0 ≤ B g` and `hB : ∀ g, B (g * a) = B g`;
- a type `ι`, `F Fw Fp : ι → G → ℂ` with `hF : ∀ i, F i = Fw i + Fp i`;
- `pw pp : ι → ℂ[X]`, `Nw Np : ℕ` and `θ` with `hθ : θ < 1`, `hpw : ∀ i, (pw i).Monic`,
  `hpp : ∀ i, (pp i).Monic`, `hNw : ∀ i, (pw i).natDegree = Nw`,
  `hNp : ∀ i, (pp i).natDegree = Np`, `hrw : ∀ i, ∀ z ∈ (pw i).roots, ‖z‖ = 1`,
  `hrp : ∀ i, ∀ z ∈ (pp i).roots, ‖z‖ ≤ θ`,
  `hannw : ∀ i, aeval (GroupAction.rightFunctions a) (pw i) (Fw i) = 0` and
  `hannp : ∀ i, aeval (GroupAction.rightFunctions a) (pp i) (Fp i) = 0`;
- `t` with `ht : 0 ≤ t`, `C₁ : ℝ`, `d : ℕ` and
  `h1 : ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, t ≤ α (H g)) →
  ‖F i g‖ ≤ C₁ * B g * (1 + σ g) ^ d` (a bound on the constant term, not on its positive part);
- `δ` with `hδ : 0 < δ`, `C₀ : ℝ` and
  `h0 : ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, δ * ‖H g‖ ≤ α (H g)) →
  ‖H g‖ ≤ t / δ → ‖Fp i g‖ ≤ C₀ * B g`.

Conclusion: `∃ ε > 0, ∃ C : ℝ, ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) →
(∀ α ∈ S, δ * ‖H g‖ ≤ α (H g)) → ‖Fp i g‖ ≤ C * B g * Real.exp (-(ε * ‖H g‖))`.

Under the dictionary of `PositivePartDecay.md`, `h1` is the bound on `(E^G_P sp_χ ψ)_{P'}` that
the source derives from I.5, Proposition I.4.3, Lemma VI.2.2 and Lemma II.1.1 (not derived here),
and the conclusion is Lemma VI.2.3 for the family `χ ∈ Im X(M)`.

## Proof

`IsCoeffBounded.mul`: the coefficient of `Xⁿ` in `f g` is `Σ_{k ≤ n} f_k g_{n−k}`; bounding
`|f_k|` by `B₁` and reflecting the sum leaves `B₁ Σ_{j ≤ n} |g_j| ≤ B₁ (d₂ + 1) B₂`.
`isCoeffBounded_of_roots` writes the coefficients as `± e_{N−k}` of the roots
(`Multiset.prod_X_sub_C_coeff`) and uses `norm_esymm_le`. `pow_le_norm_eval` writes `p(w)` as
`∏ (w − z)` with `|w − z| ≥ |z| − |w| ≥ 1 − θ`.

`dvd_X_sub_C_mul_invXSubCMod_sub_one`: `(X − w)(p /ₘ (X − w)) = p − p(w)`, so
`(X − w) invXSubCMod p w − 1 = −p(w)^{−1} p`. Its coefficients are
`−p(w)^{−1} Σ_{i=k+1}^{N} w^{i−k−1} p_i` (`coeff_divByMonic_X_sub_C`), bounded by
`(1 − θ)^{−N} N 2^N` since `|w| ≤ 1` and `|p_i| ≤ 2^N`.

`exists_projection_polynomial`: with `θ' = max θ 0`, put `R = ∏_{w ∈ roots(p_+)} invXSubCMod p_w w`
and `E = R p_+`. Then `p_+ ∣ E`, and `E = ∏_w (X − w) invXSubCMod p_w w`, a product of factors
`≡ 1` modulo `p_w`, so `p_w ∣ E − 1`. `R` has degree at most `N_+ (N_w − 1)` and coefficients
at most `((N_w − 1 + 1) B_q)^{N_+}` (`isCoeffBounded_multiset_prod` with the bound `B_q` of
`invXSubCMod`), and `p_+` has coefficients at most `2^{N_+}`; `IsCoeffBounded.mul` gives the
constant `C = (N_+ + 1) ((N_w − 1 + 1) B_q)^{N_+} 2^{N_+}`, which depends only on `N_w`, `N_+`
and `θ'`.

`aeval_apply_eq_of_dvd`: writing `E = p_+ u` and `E = 1 + s p_w`, `E(T)` kills `x_+` and fixes
`x_w`. `exists_norm_le_sum_translates` evaluates `F^w = E(ρ(a)) F = Σ_i e_i ρ(a)^i F` at `m`
(`aeval_eq_sum_range'`, `ρ(a)^i F (m) = F(m aⁱ)`) and bounds `|e_i| ≤ C`.

`exists_norm_le_exp_of_decomposition`: on the shifted chamber, each `g aⁿ` stays in the chamber
and `‖F i (g aⁿ)‖ ≤ |C₁| (1 + σ(aⁿ))^d B(g) (1 + σ(g))^d` (from `h1`, `B(g aⁿ) = B(g)` and
`1 + σ(g aⁿ) ≤ (1 + σ(g))(1 + σ(aⁿ))`). Then
`‖F^+ i g‖ ≤ ‖F i g‖ + ‖F^w i g‖ ≤ C₁' B(g) (1 + σ(g))^d` with
`C₁' = |C₁| (1 + σ(1))^d + |C_w| Σ_{n < K} |C₁| (1 + σ(aⁿ))^d`, `C_w` the constant of
`exists_norm_le_sum_translates`. This is estimate (1) for the positive parts, and
`exists_norm_le_exp_of_aeval_eq_zero` applied to `F^+ i` and `pp i` gives the conclusion.
