# Compact Harish-Chandra restrictions to boxes on the weighted Siegel space

Module `Langlands.Global.AdelicLocalFinitenessBoxOperators`. It transports the compact
Harish-Chandra restriction of `AdelicHarishChandraBoundaryCompact` from the rational quotient
`Z = P₀(F) \ G(𝔸)` to the fundamental domain of `P₀(F)` in `G(𝔸)` with the Siegel weight in
chamber coordinates (`siegelHaar`, module `AdelicLocalFinitenessResidualOperators`), for the
boxes `orthantBox` of `AdelicLocalFinitenessChamberEmbedding`.

## Auxiliary results

- `WeightedSiegel.frameMeasure_restrict_height`: restricting the frame measure of a height region
  `S₁` to the heights in a Borel set `S₂` gives the frame measure of `S₁ ∩ S₂` (restriction of a
  measure with density is the measure with the indicator density, and the indicator of the
  chamber density of `S₁` on `H⁻¹(S₂)` is the chamber density of `S₁ ∩ S₂`).
- `orthantBox_eq_preimage`: `orthantBox c τ J ε m = c⁻¹(orthantBox id τ J ε m)`;
  `measurableSet_orthantBox_id`, `measurableSet_siegelRegion`: the coordinate box and the Siegel
  region are measurable.
- `boxHeightRegion e τ J ε m = e⁻¹(siegelRegion τ) ∩ e⁻¹(orthantBox id τ J ε m)`: the heights of the
  box inside the Siegel region, for a coordinate map `e` on the real dual of `P₀`. Its preimage in
  `Z` is the slab region to which `adelicHarishChandraBoundaryCompact` is applied below.
- `hcComponent_eq_alternatingSum_componentFoldCT`: for a measurable left `P₀(F)`-invariant `φ`,
  the Harish-Chandra component `𝓕.hcComponent P φ = ∑_{S ⊆ P} (−1)^{|P ∖ S|} C_S φ` equals the
  alternating sum of the folded constant terms `componentFoldCT S φ` (the bridge
  `constantTerm_eq_foldConstantTerm`). Consequently
  `hcComponent_minimalParabolicImage_mul`: `𝓕.hcComponent P φ` is left `P₀(F)`-invariant
  (`componentFoldCT_invariant`).
- `toFun_measurable_invariant`: the function of an element of `𝔉^R_L` is measurable (it is
  continuous) and left invariant under `P₀(F)` (it is invariant under `G(F)`,
  `evaluate_rational_mul`).

## `exists_boxBoundaryOperator`

Hypotheses: those of `AdelicHarishChandraBoundaryCompactStatement` (connected reductive `G`, a
Siegel setup, the coordinates `dT`, `e` and positive steps with the root and central
normalizations) and an Iwasawa compact `K` for `P₀`.

Conclusion: there is `c > 0` such that for all rates `ra_β, rb_j ≥ c`, thresholds `τ`, every finset
`P` (with `J_P = P ∩ Δ`), orthant `ε`, degrees `m`, growth exponent `R ≥ 0`, open level `L`, complex
Hilbert space `E` and continuous linear `smooth : E → 𝔉^R_L`, there is a compact operator

```
T : E →L[ℂ] L²( siegelHaar restricted to orthantBox (chamberCoords hK e) τ J_P ε m )
```

with `T q = 𝓕.hcComponent P (smooth q)` almost everywhere.

Proof. Let `c` be the rate bound of `adelicHarishChandraBoundaryCompact`. The set
`S = H₀⁻¹(boxHeightRegion e τ J_P ε m)` of `Z` is measurable and lies in a slab: on it all root
coordinates are `> τ_β`, the root coordinates outside `J_P` are `≤ τ_β + m_β`, and the central
coordinates satisfy `|y_j| ≤ m_j + 1` (from `0 < ±y_j + 1 ≤ m_j`). The theorem gives a compact
`T₀ : E → L²(domainMeasure ell S)`, `ell = localFinitenessLogWeight ra rb ∘ e`, with
`T₀ q (z) = hcComponent P (smooth q) (out z)` almost everywhere. The Siegel measure restricted to
the box is the frame measure of `e⁻¹(siegelRegion τ) ∩ e⁻¹(box)`
(`frameMeasure_eq_domainWeightedHaar`, `frameMeasure_restrict_height`), which the quotient map
carries to `domainMeasure ell S` (`measurePreserving_mk_frameMeasure`). So `T` is `T₀` followed by
composition with the quotient map, an isometry, and is compact. Almost everywhere
`T q (g) = hcComponent P (smooth q) (out (mk g))`; the representative `out (mk g)` is `l g` with
`l ∈ P₀(F)`, and the component is `P₀(F)`-invariant.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234 (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`),
§7.4, Lemma (3), p. 216 (the operator `f ↦ (δ(h)f)_P^S|_{S_P^B}` into the weighted space of the
boundary region is Hilbert–Schmidt, hence compact), used for the operator `ν_s` in §7.6, pp. 219–220, and with the central
orthants in §7.7, pp. 220–221. The boxes here are those of `orthantBox`; the compactness itself
is the Library theorem `adelicHarishChandraBoundaryCompact`.
