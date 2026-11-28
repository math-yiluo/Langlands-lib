# Upper logarithmic height on a Siegel chamber

Module `Langlands.Global.AdelicSiegelChamberHeightComparisonProof`, namespace `Langlands.Global`.
The theorem `siegelChamberHeightComparison` proves `SiegelChamberHeightComparisonStatement`
(module `Langlands.Global.AdelicSiegelChamberGeometryStatement`): for an algebraic Siegel setup
`(T, i, ν, T₀, j)` of a connected reductive `G` over a number field, a closed matrix embedding
`rho` and a compact `Ω ⊆ G(𝔸)`, there are rational characters `χ_1, …, χ_r` of `G` and `C` with

`adelicLogHeight F G rho (z b ω) ≤ C (1 + R)`

for `z ∈ A_G` (`RestrictionSplitCentre.canonicalSubgroup F G`), `b` in the positive torus
`A_{T₀}` (mapped to `G(𝔸)` by `positiveMap`), `ω ∈ Ω` and every `R ≥ 0` bounding the absolute
values of `log |β(b)|` for the simple relative roots `β` and of `log ‖χ_k(z b ω)‖` for all `k`.

## Proof

**Matrix size zero.** If `N = 0`, the adelic points of `GL_0` form a subsingleton, so
`adelicSourceNorm` and hence `adelicLogHeight` are constant. The proof takes `r = 0` and
`C = adelicLogHeight F G rho 1`, which is at least `1`, and uses `1 ≤ 1 + R`.

**Matrix size `N > 0`.**

1. *Characters.* `exists_finite_ambient_characters_span` gives a finite set `S` of restrictions
   to `T` of rational characters of `G` such that the simple relative roots together with `S`
   span `ℚ ⊗ X^*(T)`. The characters `χ_1, …, χ_r` are chosen preimages of the elements of `S`.
2. *Constants.* `adelicPositiveTorusLogHeightBound`, applied to the maximal split torus `T`
   (split by `IsMaximalSplitTorus`) and this spanning set, gives `A` and `rate` with
   `adelicHeight(i(a)) ≤ A · exp(rate · M)` for every `a` in the positive torus of `T` whose
   logarithms on all the spanning characters are at most `M ≥ 0` in absolute value. By
   continuity (`continuous_adelicHeight`, `continuous_characterLog_eval`) and compactness,
   `adelicHeight ≤ B` on `Ω` with `B = max 1 B₀`, and `|log ‖χ_k(ω)‖| ≤ D_k` on `Ω`; put
   `D = ∑_k max 0 D_k`. The constant is `C = max (1 + log (A B) + rate · D) rate`.
3. *The point `z b` comes from the positive torus of `T`.* `IsSiegelAlgebraicSetup` supplies a
   torus `Z` with `zc : Z → T` such that `Z → T → G` is a split component (`IsSplitComponent`),
   in particular a central split torus, and `imageSubgroup_eq_canonicalSubgroup` identifies its
   positive image with `A_G`. So `z` is the image of a point `a` of the positive torus of `Z`,
   and `z b` is the image under `i` of the point `ab = a_T · b_T` of the positive torus of `T`,
   where `a_T` and `b_T` are the images of `a` under `zc` and of `b` under `j`.
4. *Simple-root coordinates.* A relative root restricts trivially along `zc`, since `Z` is a
   central split torus (`root_restrict_eq_zero_of_isCentral`). Since `characterLog` is additive and natural
   (`characterLog_mul`, `characterLog_map`), the logarithm of a simple root `β` at `ab` equals
   `log |β(b)|`, so its absolute value is at most `R ≤ R + D`.
5. *Ambient-character coordinates.* For `ψ ∈ S`, the restriction of `χ_k` to `T`, the logarithm
   of `ψ` at `ab` equals `log ‖χ_k(z b)‖ = log ‖χ_k(z b ω)‖ − log ‖χ_k(ω)‖`, whose absolute value
   is at most `R + D_k ≤ R + D`.
6. *Height.* By step 2 with `M = R + D`, `adelicHeight(z b) ≤ A · exp(rate (R + D))`.
   Submultiplicativity (`adelicHeight_mul_le`) and the bound on `Ω` give
   `adelicHeight(z b ω) ≤ A B · exp(rate (R + D))`.
7. *Logarithm.* `adelicHeight` is at least `1` for `N > 0` (`one_le_adelicHeight`) and equals
   `N^{∑_v m_v}` times `adelicSourceNorm` (`adelicHeight_eq_scalar_mul_sourceNorm`), a factor at
   least `1`. Hence `max 1 (adelicSourceNorm (z b ω)) ≤ adelicHeight(z b ω)`, and taking
   logarithms, `adelicLogHeight F G rho (z b ω) ≤ 1 + log (A B) + rate · D + rate · R`, which is
   at most `C + C R = C (1 + R)`.

The route differs from the sketch in the statement's page: instead of bounding the heights of
`z` and `b` separately, the proof applies the positive-torus height bound once to the product
`z b`, viewed in the positive torus of the maximal split torus `T`, with the simple roots and the
ambient characters as its spanning coordinates.

## Source

This is the upper half of the comparison `σ(g) ∼ 1 + ‖H_0(g)‖` on Siegel domains, where
`σ(g) = 1 + log ‖g‖`, in P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023) 109107, §2, (2.8), p. 8 of the published PDF, written in the coordinates
`log |β(b)|` and `log ‖χ(z b ω)‖`.
