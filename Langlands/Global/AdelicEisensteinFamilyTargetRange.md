# The family comparison under a change of presentation of the target parabolic

Module `Langlands.Global.AdelicEisensteinFamilyTargetRange` proves
`FamilyRegularComparison.of_targetRange`.

## Statement

Let `q₁ : Q₁ → G` and `q₂ : Q₂ → G` be parabolics identified by `e : Q₂ ≅ Q₁` with
`e ≫ q₁ = q₂`, with the same image, radicals `iV₁ ≫ q₁`, `iV₂ ≫ q₂` with the same image, and
Levis `l₁ ≫ q₁`, `l₂ ≫ q₂` with the same image. Let `r₁`, `r₂` be arbitrary root presentations
of `(q₁, l₁)` and `(q₂, l₂)`; they may use different maximal split tori. Assume:

- the Weyl data correspond: `weylParameter l c₂ π₂ λ = e^* (weylParameter l c₁ π₁ λ)` for every
  `λ`, where `e^*` is restriction along `e`;
- regularity is comparable: for every `R` there is `R'` such that every `μ` with `e^* μ`
  `R'`-regular for `r₂` is `R`-regular for `r₁`.

If `K` has Iwasawa coverage for `P`, `Q₁` and `Q₂`, then the family comparison (module
`Langlands.Global.AdelicEisensteinFamilyRegularComparison`) for `(q₂, r₂, π₂, c₂)` implies the
family comparison for `(q₁, r₁, π₁, c₁)`, with the same `P`-side data and Weyl point `w`.

## Proof

Given `R`, choose `R'` from the regularity comparison and apply the comparison for `q₂` with
threshold `R'`. The ingredients are:

- the inducing spaces of `Q₁` and `Q₂` agree (`parabolicQuotientSubgroup_eq_of_range_eq`), so
  the target forms `ψ i` serve both;
- `E_{Q₁}(ψ, μ) = E_{Q₂}(ψ, e^* μ)` (`IsIwasawaCompact.eisensteinSeries_eq_of_range_eq`, module
  `Langlands.Global.AdelicEisensteinParabolicRangeTransport`);
- the height factors correspond, `H_{Q₂}^{e^* μ} = H_{Q₁}^μ` (`IsIwasawaCompact.heightPower_restrict`);
  together with the Weyl data hypothesis and
  `IsIwasawaCompact.intertwiningIntegral_eq_of_range_eq_of_twist`, this gives
  `M_{Q₁}(w, λ)φ = M_{Q₂}(w, λ)φ`.

On the resulting patch, `weylParameter l c₂ π₂ λ = e^*(weylParameter l c₁ π₁ λ)` is
`R'`-regular for `r₂`, so `weylParameter l c₁ π₁ λ` is `R`-regular for `r₁`, and the
`Q₂`-series are the `Q₁`-series.

## Source

Provenance: derived. Bernstein–Lapid's regularity condition (J. Bernstein and E. Lapid, *On the
meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §2.2, p. 191, registered
as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`) depends only on the parabolic.
The Library's `ParabolicRootPresentation.IsRegularParameter` depends on a presentation, so the
comparability of thresholds is a hypothesis here. In module
`Langlands.Global.AdelicEisensteinFamilyStandardTarget` it is obtained from
`RootPresentationRegularityComparisonStatement` (module
`Langlands.Global.AdelicEisensteinRegularityPresentationComparisonStatement`), which is a
hypothesis of the theorem there.
