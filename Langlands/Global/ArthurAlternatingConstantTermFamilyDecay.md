# Family decay of the alternating constant terms on the sigma region

**Sources.** J. Arthur, *A trace formula for reductive groups II* (1980),
`arthur-1980-trace-formula-reductive-groups-II`, Lemma 1.4 and the estimate (1.2), printed
pp. 95–97 (PDF pp. 10–12); J. Arthur, *An introduction to the trace formula* (2005),
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, (13.7)–(13.8), printed pp. 71–72
(PDF pp. 83–84).

The module `Langlands.Global.ArthurAlternatingConstantTermFamilyDecay` proves the family version of
the estimate of Arthur's alternating constant terms on the region where the sigma function of the
pair `R ⊆ S` is supported. All declarations are in `Langlands.Global.ArthurTruncation`.

## Statement

`alternatingConstantTerm_familyDecay`: let `N > 0`, `R ⊆ S ⊆ Δ₀`, `T₁, T`, compact sets
`Ω ⊆ P₀(𝔸)` and `K' ⊆ G(𝔸)¹`, an open compact subgroup `K₀` of `G(𝔸_f)` and exponents `n₀`, `m`.
Write `H = adelicHeight F G rho`. There are a word length `nw` and a constant `C ≥ 0` with the
following property. Let `p ∈ Ω`, `a ∈ sigmaTorusRegion R S T₁ T` and `k ∈ K'` with
`p a k ∈ G(𝔸)¹`. Let `(Ω', m)` be any measure space and `φ o` (`o ∈ Ω'`) functions on `G(𝔸)¹`
satisfying `IsNormOneCr At r K₀` for some `r ≥ nw`, jointly measurable in `(o, y)`. If for some
`M ∈ [0, ∞]` and every word `w` of length at most `nw`

`∫_{Ω'} ‖D_w (φ o) y‖ dm ≤ H(y)^{n₀} M` for all `y ∈ G(𝔸)¹`,

then

`(∫_{Ω'} ‖alternatingConstantTerm R S (normOneExtension hG (φ o)) (p a k)‖ dm) · H(p a k)^m ≤ C M`.

The word length `nw` and `C` depend on the data, `n₀` and `m`, but not on the family.

## Proof

The proof follows the sup-norm argument for a single function, with family integrals in place of
absolute values. Let `g o w` be `alternatingWordSystem` with word length `nw`; then `g o []` is the
alternating constant term of the extension of `φ o`, and the word system satisfies the hypotheses of
`normOneFamilyDecayModulo` (module `Langlands.Global.ArthurAlternatingWordSystem`).

`sigmaTorusRegion_bounds` gives `B`, `C₀` and `t₀` such that on the region every root of `S` is
`≥ −B` in logarithmic size, and `H(a) ≤ C₀ exp(t₀ L)` whenever every root of `S \ R` is at most
`L ≥ 0`. Choose `nw > d_F t₀ (n₀ + m)`, where `d_F = [F : ℚ]`.

For each `α ∈ S \ R`, `exists_standardLeviContractionModulo_normOne` gives a smooth map `Ψ` into
`G(F∞)` with values in `G(F∞)¹`, `Ψ(0) = 1`, satisfying the contraction hypothesis for the radical of
the maximal parabolic `Δ₀ \ {α}`, the points `a` of the weak chamber of `S`, the radical of `S` as
`L₀` and the contraction factor `ε(a) = relativeCharacterDecay α a`, which is bounded on the chamber.
`normOneFamilyDecayModulo` with `nw` steps gives a compact `K₁ ⊇ K'` in `G(𝔸)¹` and `C₁` with

`∫ ‖g o [] (p a k)‖ ≤ C₁ ε(a)^{nw} sup_{k' ∈ K₁, |w| = nw} ∫ ‖g o w (p a k')‖`.

By `exists_lintegral_alternatingWordSystem_le`, each integral on the right is at most
`Cg H(p a k')^{n₀} M`.

At the point `a`, let `L` be the largest of `0` and the logarithmic sizes of the roots of `S \ R`.
If `L = 0`, then `H(p a k) ≤ E₀ C₀` by compactness of `Ω` and `K'` (`H(p x k) ≤ E H(x)`), and the
bound `∫ ‖g o [] (p a k)‖ ≤ Cg H(p a k)^{n₀} M` suffices. Otherwise `L` is the size of a root `α`,
`H(p a k') ≤ Dα exp(t₀ L)` for `k' ∈ K₁`, and `ε(a)^{nw} = exp(−nw L / d_F)`
(`relativeCharacterDecay_pow_eq_exp`). By the choice of `nw`,
`ε(a)^{nw} · (Dα exp(t₀ L))^{n₀ + m} ≤ Dα^{n₀ + m}`. The constant `C` is the constant of the first
case plus the sum over `α ∈ S \ R` of the constants of the second case.
