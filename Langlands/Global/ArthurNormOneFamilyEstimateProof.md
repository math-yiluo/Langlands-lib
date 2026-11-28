# The family estimate (13.5)–(13.6) for every compact Iwasawa subgroup

**Sources.** J. Arthur, *An introduction to the trace formula* (2005),
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, Proposition 13.2(b), (13.5)–(13.8),
printed pp. 70–72 (PDF pp. 82–84); J. Arthur, *A trace formula for reductive groups II* (1980),
`arthur-1980-trace-formula-reductive-groups-II`, Lemma 1.4 and its proof, printed pp. 95–97
(PDF pp. 10–12).

The module `Langlands.Global.ArthurNormOneFamilyEstimateProof` proves the family estimate
`IsNormOneFamilyEstimate` (module `Langlands.Global.ArthurTruncationRapidDecayReduction`) for every
compact subgroup `K` with `P₀(𝔸_F) K = G(𝔸_F)`. All declarations are in
`Langlands.Global.ArthurTruncation`.

## Main theorem

`exists_isNormOneFamilyEstimate`: let `G` be connected reductive over a number field `F`, `i` a
maximal split torus, `ν` a generic cocharacter, `D` reflection data, `K` a subgroup with
`IsIwasawaCompact (Standard.parabolicHom i ν ∅) K`, `hρ` the comparison, `At` an embedded Lie atlas
on `G(F∞)¹` and `rho` a closed matrix realization in `GL_N` with `N > 0`. Then there is `c` such
that `IsNormOneFamilyEstimate At hG hi D hK hρ rho T` holds for every `T` with `β(T) > c` for all
simple relative roots `β`.

## Proof

**Expansion.** `iwasawaSiegelCovering` and `iwasawaSiegelReduction` give compact factors `C₀` and
`T₀` for which `arthurTruncationSigmaExpansion` applies: there is `c` such that for `β(T) > c`, every
continuous left `G(F)`-invariant `f` and every `x`, the truncation of `f` at `x` is the sum over
`R ⊆ S ⊆ Δ₀` and the rational cosets `d ∈ P_R(F) \ G(F)` of `W_{R,S}(δ_d x) · alternatingConstantTerm R S f (δ_d x)`,
where `W` is `siegelSigmaCoefficient` and `δ_d` a representative. For each `x` only finitely many
cosets have `W ≠ 0`, and this finite set `F_{R,S}(x)` does not depend on `f`.

Fix the Siegel set data `C`, `T₁`, the exponents `n, n₀` and the level `K₀`.
`arthurSiegelNormMinimality` gives `Cmin` with `H(x) ≤ Cmin H(γ x)` for `x` in the Siegel set and
`γ ∈ G(F)`; `rationalAdelicHeightSummability` and `siegelCosetSumDecay` give an exponent `m` and a
constant `Csum` that turn termwise bounds `|b_j| H(γ_j x)^m ≤ B` over distinct rational points
`γ_j` into `|∑ b_j| H(x)^n ≤ Csum B`, for `x` satisfying the minimality inequality. For each pair `R ⊆ S`,
`exists_sigmaCoset_representatives_familyBound` gives a word length `nw(R, S)` and a constant
`B(R, S)`. The order is `r = ∑ nw(R, S) + 1`, the operators are the words of length at most `r`
(`normOneWordsUpTo`), and the constant is `∑ Csum B(R, S) + 1`.

**Measurability.** Let `x ∈ G(𝔸_F)¹` lie in the Siegel set. By `truncation_congr_on_normOne`, the
truncation of the zero extension of `φ o` at `x` equals the truncation of the continuous extension
`normOneExtensionCRF`, so it is the finite sum above with `f = normOneExtension hG (φ o)`. Each
term is measurable in `o` (`measurable_alternatingConstantTerm_normOneExtension`).

**Bound.** Let `M` be the supremum on the right side of the estimate. If `M = ∞` there is nothing
to prove. Otherwise, for a word `w` of length at most `r` and `y ∈ G(𝔸_F)¹`,
`∫ ‖D_w (φ o) y‖ ≤ ‖y‖^{n₀} M ≤ H(y)^{n₀} M`, since `normOneDifferential At (normOneWord w)` is
`D_w` (`normOneDifferential_normOneWord`) and the source norm `‖y‖` is at most the height
`H = adelicHeight F G rho`. For a pair `R ⊆ S`, write `I_d` for the family integral of the `d`-th
term. `exists_sigmaCoset_representatives_familyBound` gives distinct rational points `γ_d` with
`I_d H(γ_d x)^m ≤ B(R, S) M`; these are finite reals, and `siegelCosetSumDecay` applied to the
finite family `I_d`, `d ∈ F_{R,S}(x)`, gives `(∑_d I_d) H(x)^n ≤ Csum B(R, S) M`. The triangle
inequality and `H(x) ≥ ‖x‖` complete the estimate.

## The sigma summands

`exists_sigmaCoset_representatives_familyBound`: for `R ⊆ S ⊆ Δ₀` there are `nw` and `B ≥ 0` such
that for every `x ∈ G(𝔸_F)¹` there is an injective choice `d ↦ γ_d ∈ G(F)` of rational points, one
for each coset `d`, independent of the family, with

`(∫ ‖W_{R,S}(δ_d x) alternatingConstantTerm R S (normOneExtension hG (φ o)) (δ_d x)‖ dm) · H(γ_d x)^m ≤ B M`

for every family of class `C^r`, `r ≥ nw`, whose word derivatives of length at most `nw` satisfy
`∫ ‖D_w (φ o) y‖ ≤ H(y)^{n₀} M` on `G(𝔸_F)¹`. If `W(δ_d x) = 0` take `γ_d = δ_d`. Otherwise the
Siegel indicator gives `z ∈ P_R(F)` with `z δ_d x` in the truncated Siegel set, and
`γ_d = z δ_d`; then `γ_d x = p a k` with `p` in the compact prefix, `a` in `sigmaTorusRegion` and
`k ∈ K` (`exists_sigmaTorusRegion_of_mem'`, using that sigma is invariant under `P_R(F)`), the
alternating constant term is invariant under `z` (`alternatingConstantTerm_mul_left'`), and
`alternatingConstantTerm_familyDecay` applies. The auxiliary lemmas `sigma_height_mul_left'`,
`alternatingConstantTerm_mul_left'`, `compactPrefix_subset_minimalParabolic'` and
`exists_sigmaTorusRegion_of_mem'` are private to this module.
