# Finiteness of `Θ^H_G` for the rational points of a connected reductive group: Waldspurger VIII.5

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFiniteness`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnramifiedCharacterExtension`:
  `finite_discreteSeriesFixedOrbits_of_finite_central` and
  `finite_discreteSeriesFixedOrbits_of_finiteDimensional` (the abstract finiteness theorems for
  `Θ^H_G` without an extension hypothesis); through it
  `Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteSeriesOrbitFiniteness`
  (`discreteSeriesCentralFixed`, `discreteSeriesFixedOrbits`),
  `Langlands.Representation.Plancherel.DiscreteSeriesOrbits` (`DiscreteSeriesOrbitClass`),
  `coefficientFunctionSpace` and `IsBiInvariant`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralQuotientGeneration`:
  `isCompact_rationalNormKernelPart` (`A ∩ G¹` is compact for a closed central subgroup `A` of
  `G(F)`); through it `Langlands.Representation.Plancherel.RationalCharacterTopology`
  (`compactSubgroup_le_rationalCommonNormKernel`),
  `Langlands.Representation.Plancherel.RationalCharacterValuation` (`rationalNormCharacters`,
  `rationalCommonNormKernel`), `Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup`
  (`isClosedEmbedding_rationalPointMap`), `Langlands.AlgebraicGeometry.PointTopology.RationalPoints`
  (`rationalPointTopology`) and `Langlands.GroupScheme.Rational.Characters` (`IsCentral`,
  `IsCentral.range_le_center`, `IsSplitComponent`, `IsSplitComponent.isCentralSplitTorus`,
  `IsCentralSplitTorus.isCentral`, `IsCentralSplitTorus.isSplitSubtorus`);
- `Langlands.Representation.Plancherel.RationalTwistStabilizer`:
  `rationalPoints_nonarchimedeanGroup` (the canonical topology on `G(F)` makes it a
  nonarchimedean group); through it `Langlands.BruhatTits.localField_t2Space`.

These Library names are read in the namespaces `Langlands.Plancherel`, `Langlands.GroupScheme`
and `Langlands.AlgebraicGeometry.PointTopology`. From Mathlib it also uses
`Subgroup.normal_of_le_center`, `MonoidHom.coe_range`,
`Topology.IsClosedEmbedding.isClosed_range` and `AlgebraicGeometry.isAffine_of_isAffineHom`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus 234.

- I.1, printed pp. 238–239 (PDF pp. 4–5): "On note `F` un corps local non archimédien de corps
  résiduel fini `F_q`. [...] Soit `G` un groupe linéaire algébrique réductif et connexe." and,
  for a semi-standard Levi subgroup `M` (in particular `M = G`), "on note `A_M` le plus grand
  tore déployé dans le centre de `M`". Groups are identified with their `F`-points ("soit `A` un
  tore déployé" means the group of `F`-points of a split torus). On printed p. 239:
  "On pose `G¹ = ⋂_{χ ∈ Rat(G)} Ker |χ|_F`, `X(G) = Hom(G/G¹, ℂ*)`" and
  "On pose `Im X(G) = {χ ∈ X(G); Re(χ) = 0}`. C'est le sous-ensemble des éléments unitaires de
  `X(G)`."
- VIII.1, printed p. 321 (PDF p. 87): "Notons `Θ_G` l'ensemble des orbites dans `E₂(G)` pour
  l'action de `Im X(G)`. [...] Soit `H` un sous-groupe ouvert compact de `G`. [...] On note `Θ^H`
  l'ensemble des `(O, P)` tels que cette propriété soit vérifiée pour un (ou pour tout)
  `(ω, E) ∈ O`. On pose `Θ^H_G = Θ_G ∩ Θ^H`." Then "Théorème VIII.1.2. Pour tout sous-groupe
  ouvert compact `H` de `G`, `Θ^H_G` est fini."
- VIII.5, printed pp. 331–332 (PDF pp. 97–98): the proof of Theorem VIII.1.2, which reduces the
  finiteness of `Θ^H_G` to the finiteness of the sets `E₂(G)^H_χ` for `χ` in a finite set of
  representatives of `Â^H_G / Im X(G)`, and then derives that finiteness from
  `⨁_{ω ∈ E₂(G)^H_χ} A(ω)^{H×H} ⊂ p_χ(°C_H)` (Theorem VIII.4.2), `A(ω)^{H×H} ≠ {0}`, and the
  finite dimension of `p_χ(°C_H)` (Proposition VIII.4.1). The full passage is quoted in
  `DiscreteSeriesOrbitFiniteness.md`.

This module specializes the abstract reduction of `DiscreteSeriesOrbitFiniteness` and
`UnramifiedCharacterExtension` to Waldspurger's group `G(F)`: it discharges the hypotheses
`H ≤ G¹` and "`A_G ∩ G¹` compact" (and, through `UnramifiedCharacterExtension`, the extension
of unitary characters to `Im X(G)`). The remaining hypothesis is the finite-dimensional space
`p_χ(°C_H)` of Proposition VIII.4.1 and Theorem VIII.4.2 (or directly the finiteness of the
`E₂(G)^H_χ`).

## Scope: the actual group and explicit hypotheses

Throughout, `F` is a nonarchimedean local field (`[IsNonarchimedeanLocalField F]`), `G` is a
group scheme over `Spec F` with `[IsAffine G.X.left]` and `[LocallyOfFiniteType G.X.hom]`, and
`G(F) = GroupScheme.rationalPoints G` carries the canonical topology `rationalPointTopology F G.X`
(a nonarchimedean group by `rationalPoints_nonarchimedeanGroup`). `T` is a commutative group
scheme over `Spec F` and `s : T ⟶ G` a homomorphism; the image
`(GroupScheme.rationalPoints.map s).range` of `T(F)` in `G(F)` plays the role of `A_G`. The data
`ν` of the abstract modules is `fun ψ => (rationalNormCharacters G ψ).toMul`, the normalized
absolute values `|ψ|_F` of the rational characters `ψ ∈ Rat(G)`; so `commonNormKernel ν` is
Waldspurger's `G¹` (the Library's `rationalCommonNormKernel G`) and
`unitaryUnramifiedCharacters ν` is `Im X(G)`.

- `isClosed_range_splitComponent G s hs`: `hs : GroupScheme.IsSplitComponent s`. It does not
  assume `[LocallyOfFiniteType G.X.hom]`.
- `isCompact_splitComponent_inf_commonNormKernel G s hG hs`:
  `hG : GroupScheme.IsConnectedReductive G`, `hs : GroupScheme.IsSplitComponent s`. It does not
  assume `[LocallyOfFiniteType G.X.hom]`.

For the remaining declarations, `G(F) ⧸ (rationalPoints.map s).range` carries a measurable
structure and `mu` is a measure on it, assumed to be a Haar measure
(`[MeasureTheory.Measure.IsHaarMeasure mu]`); discrete series are taken with respect to `mu`
(`DiscreteSeriesClass`).

- `rationalDiscreteSeriesFixedOrbits G s mu hs H` (definition): `hs : GroupScheme.IsCentral s`,
  `H : Subgroup (GroupScheme.rationalPoints G)`.
- `finite_rationalDiscreteSeriesFixedOrbits_of_finite_central G s mu hG hs H hHo hHc hfin`:
  `hG : GroupScheme.IsConnectedReductive G`, `hs : GroupScheme.IsSplitComponent s`,
  `H : Subgroup (GroupScheme.rationalPoints G)` with `hHo : IsOpen (H : Set _)` and
  `hHc : IsCompact (H : Set _)`, and `hfin`: for every continuous
  `χ : (rationalPoints.map s).range →* ℂˣ` with `‖(χ a : ℂ)‖ = 1` for all `a` and `χ a = 1`
  whenever `(a : GroupScheme.rationalPoints G) ∈ H` (so `χ ∈ Â^H_G`), the set `discreteSeriesCentralFixed _ _ mu χ H` (Waldspurger's `E₂(G)^H_χ`) is
  finite.
- `finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional G s mu hG hs H hH hF`:
  `hG`, `hs` as above, `H : OpenSubgroup (GroupScheme.rationalPoints G)` with
  `hH : IsCompact (H : Set _)`, and `hF`: for every such `χ` there is a finite-dimensional
  `E : Submodule ℂ (GroupScheme.rationalPoints G → ℂ)` containing every `H`-bi-invariant element
  of `coefficientFunctionSpace ω.val.out.obj`, for all `ω ∈ discreteSeriesCentralFixed _ _ mu χ H`.

In Waldspurger's situation `E = p_χ(°C_H)`; Proposition VIII.4.1 and Theorem VIII.4.2, which give
`hF`, are not proved here.

## Definitions

- `rationalDiscreteSeriesFixedOrbits G s mu hs H : Set (DiscreteSeriesOrbitClass _ _ mu ν)`:
  `discreteSeriesFixedOrbits` for `A = (rationalPoints.map s).range` (normal because it is
  central, `IsCentral.range_le_center` and `Subgroup.normal_of_le_center`) and
  `ν = fun ψ => (rationalNormCharacters G ψ).toMul`. It is the set of orbits, under twisting by
  `Im X(G)` (`unitaryUnramifiedCharacters ν`), of discrete-series classes of `G(F)` modulo
  `A_G(F)` that contain a class with a nonzero `H`-fixed vector. For a split component `s` and
  compact open `H`, this is Waldspurger's `Θ^H_G` (VIII.1). The definition only needs `s` to be
  central.

## Results

- `isClosed_range_splitComponent`: for a split component `s`, the image of `T(F)` in `G(F)` is
  closed. (The Library's `hasFGCompactOpenQuotients_splitComponent` contains the same argument
  inside its proof, without a separate statement.)
- `isCompact_splitComponent_inf_commonNormKernel`: for connected reductive `G` and a split
  component `s`, `A_G(F) ∩ G¹` is compact.
- `finite_rationalDiscreteSeriesFixedOrbits_of_finite_central` (**Theorem VIII.1.2 for `G(F)`
  from the finiteness of the `E₂(G)^H_χ`**): under `hG`, `hs`, `hHo`, `hHc`, `hfin`, the set
  `rationalDiscreteSeriesFixedOrbits G s mu _ H` (`Θ^H_G`) is finite.
- `finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional` (**Theorem VIII.1.2 for
  `G(F)` from Proposition VIII.4.1 and Theorem VIII.4.2**): under `hG`, `hs`, `hH`, `hF`,
  `Θ^H_G` is finite.

## Proof notes

1. `isClosed_range_splitComponent`: a split component is a central split torus, hence a split
   subtorus, whose underlying morphism is a closed immersion (`IsSplitSubtorus` includes
   `IsClosedSubgroup`). The source `T` is then affine (`isAffine_of_isAffineHom`), `F` is
   Hausdorff (`BruhatTits.localField_t2Space`), and `isClosedEmbedding_rationalPointMap` shows
   that `p ↦ p ≫ s` is a closed embedding `T(F) → G(F)` for the canonical topologies; its range,
   which is the range of `rationalPoints.map s`, is closed.
2. `isCompact_splitComponent_inf_commonNormKernel`: `isCompact_rationalNormKernelPart` applied to
   the central (`IsCentral.range_le_center`) and closed (step 1) subgroup `A_G(F)`.
3. The two finiteness theorems apply `finite_discreteSeriesFixedOrbits_of_finite_central` and
   `finite_discreteSeriesFixedOrbits_of_finiteDimensional` of `UnramifiedCharacterExtension` with
   `hH1 : H ≤ G¹` from `compactSubgroup_le_rationalCommonNormKernel` (a compact subgroup lies in
   the kernel of every `|ψ|_F`) and `hA1` from step 2.

## Relation to the Library

- `RationalDiscreteSeriesOrbitTopology` and `RationalDiscreteSeriesOrbitMeasure` use the same
  specialization (`A = (rationalPoints.map s).range` for a central `s`, the same `ν`) for the
  topology and measure on twist orbits; this module adds the finiteness of `Θ^H_G` in that
  setting, conditional on `hfin` or `hF`.
- `CoefficientIndependence` (`finite_of_isBiInvariant_coefficient_mem`) supplies the last step of
  VIII.5 through the abstract modules.

## Open obligations

- `hF` for `E = p_χ(°C_H)`: Proposition VIII.4.1 (finite dimension of `p_χ(°C_H)`) and
  Theorem VIII.4.2 (the coefficients of `ω ∈ E₂(G)_χ` lie in `p_χ(°C)`) for Waldspurger's data
  are not proved in the Library.
