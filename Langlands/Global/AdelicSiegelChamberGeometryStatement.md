# Heights on the chambers of an algebraic Siegel setup

Module `Langlands.Global.AdelicSiegelChamberGeometryStatement`, namespace `Langlands.Global`. It
states three propositions and proves nothing:

- `StandardParabolicConeHeightStatement`;
- `SiegelChamberHeightComparisonStatement`;
- `SiegelChamberGeometryStatement`, the conjunction of the two.

Both are comparisons between the logarithmic coordinates of the positive torus `A_{T₀}` of an
algebraic Siegel setup and heights on `G(𝔸)`. They are the geometric inputs of the decay of wave
packets on Siegel sets (Delorme 2023, proof of Proposition 5.4): the first converts decay in the
Iwasawa height of a standard parabolic into decay on a cone of the chamber, the second converts
decay in the chamber coordinates and the central characters into decay in `adelicLogHeight`.

## Notation

`(T, i, ν, T₀, j)` is an algebraic Siegel setup (`IsSiegelAlgebraicSetup`) of a connected
reductive `G` over a number field `F : Type`: `T` is a maximal split torus, `ν` a generic
cocharacter selecting the positive roots, `T₀` the maximal split torus of the derived group
(mapped to `T` by `j`). `Δ = simpleRelativeRoots i ν`. For `b` in the positive torus
`A_{T₀}` (`PositiveRealTorus.intrinsicSubgroup F T₀`, mapped to `G(𝔸)` by `positiveMap`),
`log |β(b)| = logNormHom F T₀ b (j ≫ β)` is the logarithm of the idele norm of `β(b)`.
`A_G = RestrictionSplitCentre.canonicalSubgroup F G`. For a rational character `χ` of `G`,
`characterLog F G g χ = log ‖χ(g)‖`. `σ = adelicLogHeight`
(`Langlands/Global/AdelicWavePacketRapidDecaySiegelReduction.lean`).

## `StandardParabolicConeHeightStatement`

Data: a subset `J ⊆ Δ` with `J ≠ Δ`, its standard parabolic `Q = Standard.parabolicScheme i ν J`,
a compact `K` with `hKQ : IsIwasawaCompact (Standard.parabolicHom i ν J) K` and Iwasawa height
`H_Q = hKQ.height`, `δ > 0`, a threshold `t : ℝ≥0ˣ` and a compact `Ω ⊆ G(𝔸)`.

Conclusion: there are `w ∈ X^*(Q) ⊗ ℝ`, `c > 0` and `C` with

`c R − C ≤ ⟨w, H_Q(z b ω)⟩` (`realParameterPairing`)

for `z ∈ A_G`, `b` in the weak simple-root chamber `|β(b)| ≥ t`
(`PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t`), `ω ∈ Ω` and every real `R` with
`|log |β(b)|| ≤ R` for all `β ∈ Δ` and `δ R ≤ log |α(b)|` for all `α ∈ Δ \ J`.

Why it holds, with `w = 2ρ_Q = 1 ⊗ det(Ad | Lie Q)`:

- `z b` is the image of a point of `Q(𝔸)` (the torus `T` and the centre lie in `Q`), so
  `H_Q(z b ω) = log_Q(z b) + H_Q(ω)` (`IsIwasawaCompact.height_map_mul`), and `H_Q` is bounded
  on `Ω`.
- `⟨2ρ_Q, log_Q(z b)⟩ = log |det(Ad(z b) | Lie Q)|`. The central `z` acts trivially on `Lie Q`.
  On `T`, `det(Ad | Lie Q)` is the sum of the roots of `T` in `Lie Q` with the dimensions of the
  root spaces as multiplicities; the roots `±β` with `β` in the span of `J` cancel (equal
  multiplicities), leaving `2ρ_Q = ∑_{β ∈ Φ⁺ \ Φ_J} m_β β`.
- Every positive root is a nonnegative integral combination of simple roots, and every
  `β ∈ Φ⁺ \ Φ_J` involves some `α ∉ J`. On the chamber `log |γ(b)| ≥ log t` for all `γ ∈ Δ`. The
  root `α ∉ J` itself occurs in `Φ⁺ \ Φ_J`, with `log |α(b)| ≥ δ R`. Hence
  `log |2ρ_Q(b)| ≥ m_α δ R − C'`.

## `SiegelChamberHeightComparisonStatement`

Data: a closed matrix embedding `rho` of `G` and a compact `Ω ⊆ G(𝔸)`.

Conclusion: there are rational characters `χ_1, …, χ_r` of `G` and `C` with

`σ(z b ω) ≤ C (1 + R)`

for `z ∈ A_G`, `b ∈ A_{T₀}`, `ω ∈ Ω` and every `R ≥ 0` with `|log |β(b)|| ≤ R` for all `β ∈ Δ`
and `|log ‖χ_k(z b ω)‖| ≤ R` for all `k`.

Why it holds:

- `σ` is built from the raw norm `adelicSourceNorm`, while the submultiplicative height is the
  dimension-scaled `adelicHeight` (`RepresentationGrowth.adelicHeight_mul_le`). For matrix size
  `N > 0` the two differ by the fixed factor `N^{∑_v m_v}` (the product over the places with
  their multiplicities), so applying the product bound twice gives
  `σ(z b ω) ≤ σ(z) + σ(b) + σ(ω) + D` with `D = 2 log N^{∑_v m_v}`; for `N = 0` the raw height is
  constant. The raw product inequality without `D` is false in general. `σ` is bounded on `Ω`,
  and `D` and that bound are absorbed into `C (1 + R)` because `R ≥ 0`.
- The simple roots span the rational characters of `T₀` up to finite index: their restrictions
  span `ℚ ⊗ X^*(T₀)` (`ratSpan_restrict_simpleRelativeRoots_eq_top`, with the Library theorems
  `relativeRootNegation` and `relativeCharacterRootComplement`). The positive-torus height bound
  `adelicPositiveTorusLogHeightBound` then gives `σ(b) ≤ C(1 + R)`.
- `A_G` is the positive image of a split central torus (`imageSubgroup_eq_canonicalSubgroup`),
  whose rational characters are spanned up to finite index by restrictions of characters of `G`
  (`RestrictionSplitCentre.canonical_finiteIndex`).
  Take `χ_k` generating `X^*(G)`. The same height bound gives `σ(z) ≤ C(1 + max_k |log ‖χ_k(z)‖|)`.
- `b` lies in the derived group, where characters of `G` are trivial, so
  `log ‖χ_k(z)‖ = log ‖χ_k(z b ω)‖ − log ‖χ_k(ω)‖`, and the last term is bounded on `Ω`.

This is the upper half of Delorme's comparison (2.8) `σ ∼ 1 + ‖H_0‖` on Siegel domains
(Mœglin–Waldspurger I.2), written in the coordinates `log |β(b)|` and `log ‖χ(z)‖`.

## Source

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF numbering): §2, p.8, `σ` and (2.8);
§5.1, p.19, the cones `𝔞^{G+}_{0,Q,δ}` of Lemmas 5.2–5.3. The structure of `Lie Q` under `T`
and the positivity of roots are standard (Borel–Tits, *Groupes réductifs*, Publ. IHÉS 27
(1965), §§4–5).

## Scope

Only the two inequalities are stated; the reverse comparison `1 + ‖H_0‖ ≪ σ` is not. Nothing is
proved here.
