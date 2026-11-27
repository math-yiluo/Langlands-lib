# Lapid's §8 limit for standard parabolic subgroups

Module `Langlands.Global.LocalWavePacketStandardReduction` states two
propositions and proves neither:

- `Langlands.Global.TruncatedStandardWavePacketLimitStatement`, the limit of
  truncated inner products of wave packets in Lapid's §8 for standard
  parabolic subgroups of one minimal pair and one compact subgroup;
- `Langlands.Global.TruncatedWavePacketStandardizationStatement`, the
  implication from it to
  `Langlands.Global.TruncatedWavePacketSectionSomeCompactLimitStatement`
  (module `Langlands.Global.LocalWavePacketSomeCompactReduction`), which is
  stated for arbitrary presented parabolic subgroups `P` and `P'`.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
  page = printed page + 9).
  - §2, p.311: a minimal parabolic `P_0` with Levi `M_0`, a maximal compact
    `K` in good position with respect to `M_0`; "a parabolic subgroup `P` will
    always mean a standard parabolic subgroup", i.e. `P ⊇ P_0`.
  - §3, p.314: `W_P`, Proposition 2 and (4).
  - Lemma 9 and its proof, p.327.
  - §8, p.328, first paragraph: by Lemma 9 it suffices to show that
    `(Λ^T Θ_{P,φ}, Λ^T Θ_{P',φ'})` converges to the right side of (4) as
    `T → ∞` in a cone.
- J. Arthur, *An introduction to the trace formula* (2005), in
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: §4, p.24 (a
  suitable maximal compact `K` with `G(𝔸) = P_0(𝔸)K`); §13, Proposition 13.1
  and the paragraph after its proof, pp.68–69 (`Λ^T` is an orthogonal
  projection on `L²`).
- A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965),
  registered as `borel-tits-1965-groupes-reductifs`: 4.13 (b), printed p.90
  (minimal parabolic `k`-subgroups are conjugate over `k`); 4.16 (iii) and
  the proof of 4.21, printed pp.91–93 (the `k`-Levi subgroups of a minimal
  parabolic `P_0` are the centralizers of the maximal split tori in `P_0`,
  and are conjugate over `k`, by 4.7).

## `TruncatedStandardWavePacketLimitStatement`

For every number field `F`, `G` connected reductive, maximal split torus
`i : T → G` and generic cocharacter `ν` (which fix the minimal parabolic
`P_0 = Standard.parabolicHom i ν ∅` and the standard parabolic subgroups
`Standard.parabolicHom i ν S.roots`, `S : StandardIndex hG hi ν`), the
proposition asserts that some `K : Subgroup (AdelicGroupPoints F G)` has the
following properties.

- `IsMaximalCompactSubgroup F G K`, `IsIwasawaCompact` for `P_0` and for every
  standard `Q`.
- For all reflection data `D` and comparisons `hρ` (and the proofs `hK₀`, `hK`
  of the Iwasawa properties, quantified again):
  - for some `C` and every `T` with `β(T) > C` for all simple roots `β`,
    `truncation hG hi D hK₀ hρ T` satisfies `IsOrthogonalL2Extension` for
    `rationalQuotientHaarMeasure F G`;
  - the limit below, for all data with respect to `K`.

The data are those of `TruncatedWavePacketSectionSomeCompactLimitStatement`
with `P = P_J` and `P' = P_{J'}` standard, for `J J' : StandardIndex hG hi ν`:

| Lapid | Lean |
|---|---|
| `P`, `M`, `U` | `Standard.parabolicHom i ν J.roots`, `Standard.leviToParabolic i ν J.roots`, `Standard.unipotentToParabolic i ν J.roots` |
| `P'` with Levi projection | the same for `J'`, and `π'` with `Standard.leviToParabolic i ν J'.roots ≫ π' = 𝟙` |
| `φ(λ) = ∑_l b_{j,l}(λ) v_{j,l}` | `v j l ∈ A^2_P` (`IsSquareIntegrableInducedForm K (hK J).isCompact …`), `b j l` entire |
| `E_P(·, φ(λ), λ)` | `E j`, meromorphic in coordinates with domain of holomorphy `DE`, equal to `∑_l b j l λ · (hK J).eisensteinSeries (v j l) λ` when `IsStandardRegularParameter D J.roots R λ` |
| `Θ = ∫ ∑_j c_j(x) E_j(i e(x)) dx` | coordinates `e : ℝⁿ ≃ X^*(P) ⊗ ℝ`, smooth `c j` vanishing outside the compact `Sx`, `{i e(x) : x ∈ Sx} ⊆ DE`, measure `spectralMeasure n` |
| `Ω(P, P')` | `Ω : Type` finite, `w`, `cw` with `IsWeylConjugation`, injective and onto `weylParameterSet` |
| `M(w, λ)φ(λ) ∈ A^2_{P'}` | `∑_l b j l λ · (hK J).intertwiningOperator (hK J') … (v j l) λ = ∑_a coeff t j a λ · ψ t j a`, with `coeff t j a` meromorphic with domain `DM ⊇ {i e(x) : x ∈ Sx}` |
| `(·,·)_{P'}` | `inducedInnerProduct K (hK J').isCompact … μM' e' β'` with `μM'` compatible with the Iwasawa decomposition of `P'` and `∫ β' = 1` |
| `T → ∞` in a cone | `T = j • v₀`, `j : ℕ → ∞`, for `v₀` with `β(v₀) > 0` for all simple roots |

The conclusion is that of `TruncatedWavePacketSectionSomeCompactLimitStatement`
with the truncation `truncation hG hi D hK₀ hρ (j • v₀)`: `y ↦ Θ(y.out)` and
`y ↦ Θ'(y.out)` are measurable and bounded on compact subsets of
`G(F) \ G(𝔸)`; their truncations are eventually in `L²` for the quotient
`μG` of Haar measure by counting measure on `G(F)`; the diagonal truncated
inner products are eventually bounded; and `(Λ^{j v₀} Θ, Λ^{j v₀} Θ')` tends to

`∫ ∑_t ∑_{j,a,j',l'} c_j(x) coeff t j a (i e(x)) conj(c'_{j'}(e'^{-1}(w_t e(x))))
conj(b'_{j',l'}(w_t i e(x))) (ψ t j a, v'_{j',l'})_{P'} dspectralMeasure(x)`,

which is `∫ ∑_{w ∈ Ω(P, P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ`, the right side of
(4).

Here "sufficiently regular" is `IsStandardRegularParameter D J.roots R`:
`R < ⟨Re λ, α^∨⟩` for the simple roots `α` outside `J`. The same `D` gives the
coroots and the truncation.

**The compact subgroup.** As in
`LocalTruncatedEisensteinFamilyInnerProductStatement`, the proposition is
existential in `K`. Lapid fixes `K` in good position with respect to `M_0`.
Arthur 2005, p.24, chooses such a `K` (admissible relative to `M_0` in the
sense of Arthur 1981, p.9). It satisfies `G(𝔸) = Q(𝔸)K` for every standard
`Q`, and Arthur proves the projection property for it.

## `TruncatedWavePacketStandardizationStatement`

`TruncatedStandardWavePacketLimitStatement →
TruncatedWavePacketSectionSomeCompactLimitStatement`. In the second statement
`P` has a presentation `r` with data `(T, i, ν, J_r)` and `P'` a presentation
`r'` with its own data `(T', i', ν', J_{r'})`. Lapid treats only standard
parabolic subgroups, and the implication is the reduction to that case.

- `P` has image `standardParabolic i ν J_r`
  (`r.isCompatible.parabolic_eq`), the image of
  `Standard.parabolicHom i ν J_r`. The compact subgroup is that of the first
  statement for `(T, i, ν) = r.data`. Its Iwasawa property for `P`, the
  Eisenstein series, intertwining operators and inner products of `P`
  transport along the isomorphism of `P` with the standard parabolic subgroup
  of the same image.
- The minimal parabolic subgroup inside `P'` given by `r'` and the pair
  `(P_0, A_0)` of `r` are conjugate under `G(F)` (Borel–Tits 4.13 (b), 4.16 and
  4.21; `minimalParabolicConjugacy` in the Library). Conjugation by a rational
  point `s` keeps `K`. Since `P_0(𝔸)K = G(𝔸)`, the conjugate parabolic
  subgroup `sP's⁻¹ ⊇ P_0` satisfies `(sP's⁻¹)(𝔸)K = G(𝔸)`, and therefore
  `P'(𝔸)K = G(𝔸)` (`IsIwasawaCompact.of_conjugate_map`). Left translation by
  the rational point `s` does not change a function on `G(F) \ G(𝔸)`. The
  Library's `standardWavePacketTransport` moves a wave packet with the
  heights of `P'` to one of `sP's⁻¹` in this way. The holomorphic families,
  their continuations and the expansions transport term by term, and the
  constant factor from the change of height is absorbed into the coefficients.
- The two notions of sufficiently regular parameters
  (`ParabolicRootPresentation.IsRegularParameter` and
  `IsStandardRegularParameter`) bound the real part away from the walls of the
  positive chamber of `𝔞_P^*`; each is implied by the other for a larger
  constant.

The module states the implication and does not prove it.
