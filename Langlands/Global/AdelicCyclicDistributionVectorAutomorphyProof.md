# Matrix coefficients of distribution vectors are generalized eigenfunctions: proof

Module `Langlands.Global.AdelicCyclicDistributionVectorAutomorphyProof` proves
`Langlands.Global.IrreducibleDistributionVectorAutomorphyStatement` (module
`Langlands.Global.AdelicCyclicDistributionVectorReduction`, whose Markdown states it and gives
its sources).

| Declaration | Kind | Content |
| --- | --- | --- |
| `irreducibleDistributionVectorAutomorphy_of_centerConjugation` | theorem | the statement, from `AdelicEnvelopingCenterConjugationStatement.{0}` |
| `irreducibleDistributionVectorAutomorphy` | theorem | `IrreducibleDistributionVectorAutomorphyStatement` |

`irreducibleDistributionVectorAutomorphy` applies the first theorem to
`Langlands.Automorphic.GroupSchemeFunctions.adelicEnvelopingCenterConjugation`, the proof of
`AdelicEnvelopingCenterConjugationStatement` in module
`Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationProof`. Both theorems use only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Setting of the proof

Introduce `F`, `G` (connected reductive), the maximal compact `K ⊆ G(𝔸)`, `hsmooth`, `hcalc`, the
Hilbert space `V`, the representation `ρ` (unitary, jointly continuous, topologically
irreducible), the distribution vector `ξ` and a smooth vector `v₀` with `ξ v₀ ≠ 0`, fixed by an
open subgroup `L` of `G(𝔸_f)`. `G(F_∞)` carries the charts
`InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth` and the Lie group structure
`InfiniteAdelicGroupPoints.smoothLieGroup`. The generic results of
`Langlands.Representation.Archimedean.ProductSmoothInfinitesimalCharacter` are applied with
`M = G(F_∞)`, `Φ = G(𝔸_f)`, `Γ = G(𝔸)`, `ιinf = ofInfinite`, `ιfin = ofFinite`: their images
commute (`AdelicGroupPoints.factors_commute`) and generate, since `g = pair (infinite g) (finite g)`
is `ofInfinite (infinite g) * ofFinite (finite g)` (`pair_mul`, `pair_projections`). Unitarity in
the form `⟪ρ g u, ρ g w⟫ = ⟪u, w⟫` comes from `ρ g ∈ unitary` by
`ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self`, and the hypothesis on `ξ` is exactly
`ProductSmoothVectors.IsDistributionForm`.

## Choice of `v`

`K_∞ = K.comap ofInfinite` is compact: it is the image under `infinite` of the compact set
`K ∩ finite⁻¹{1}`. A closed linear embedding `rho : G → GL_N`
(`affineLinearEmbeddingStatement_viaCorepresented`), the matrix of the infinite adelic points
`RepresentationGrowth.infiniteMatrix` and the place embeddings `placeMatrixRingHom` give a
continuous representation of `K_∞` on `ℂ^(N × places)`, faithful by `infiniteMatrix_injective` and
`placeMatrixRingHom_injective`. `FixedCompactFiniteChoice.exists_compactFinite_ne_zero`, applied to
the `L`-fixed vectors, gives a smooth `L`-fixed `K_∞`-finite vector `v` with `ξ v ≠ 0`; it lies in
`ProductSmoothVectors.smoothSubspace` and is nonzero. Let `Φ(g) = ξ (ρ g v)`.

## The conditions on `Φ`

- *Slices.* `functionInfiniteSlice F G Φ b` is `a ↦ ξ (ρ (ofInfinite a * ofFinite b) v)`, which
  is smooth by `ProductSmoothVectors.coefficient_contMDiff`, hence plot-smooth
  (`InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff`).
- *Smoothness* (`IsAdelicSmoothFunction`). `Φ (g * ofFinite l) = Φ g` for `l ∈ L` because `v` is
  `L`-fixed. The slices form a family with `s (b l) = s b`, and `Φ` is its evaluation
  (`pair_projections`), so `Φ` is continuous by `continuous_evaluatePlotSmoothSlices`.
- *`K_∞`-finiteness.* With `T w = (g ↦ ξ (ρ g w))`, the right translates of `Φ` by `K_∞` are the
  images under `T` of the orbit of `v`, so their span is the image of the finite-dimensional orbit
  span (`Submodule.span_image`).
- *`𝔷`-finiteness.* Let `dρ` be `SmoothVectorEnveloping.envelopingAction` for
  `ρ_∞ = ρ ∘ ofInfinite`. For `z` in the center `AdelicEnvelopingCenter F G hsmooth` and
  `g ∈ G(F_∞)`, `φ = adelicEnvelopingConjugation F G hsmooth g` extends `Ad(g)`
  (`adelicEnvelopingConjugation_ι_tmul`) and fixes `z` by `AdelicEnvelopingCenterConjugationStatement`,
  so `ProductSmoothVectors.exists_smul_of_adjointInvariant` gives `dρ(z) v = c(z) v`. Let `J` be the
  ideal `{z | dρ(z) v = 0}` of the center (an ideal because `dρ` is multiplicative). It is the
  kernel of the linear map `z ↦ dρ(z) v`, whose range lies in the line `ℂ v`, so the quotient by `J`
  is finite-dimensional (`LinearMap.quotKerEquivRange`). For `z ∈ J`,
  `plotSmoothCenterAction z` is `plotSmoothEnvelopingAction z`, in which `ι (1 ⊗ X)` acts by
  `plotSmoothDifferential X`, i.e. by `groupDirectionalValue X`
  (`plotSmoothEnvelopingAction_real_generator`); by
  `ProductSmoothVectors.coefficient_envelopingAction` it maps each slice of `Φ` to the slice of the
  coefficient of `dρ(z) v = 0`, which is zero.
- *`A_G`-character.* `A_G` is central (`RestrictionSplitCentre.canonicalSubgroup_le_center`), so for
  `a ∈ A_G` the operator `ρ a` commutes with `ρ` and is a scalar by
  `exists_eq_scalar_of_unitary_commute`; the scalar is `c(a) = ⟪v, ρ a v⟫ / ⟪v, v⟫`. The function `c`
  is continuous (joint continuity of `ρ`), multiplicative on `A_G`, and of modulus one there
  (unitarity), so `RestrictionSplitCentre.exists_realParameter_of_unitary` gives `ν` with
  `c(a) = parameterPower F G (imaginaryParameter F G ν) a`. Then
  `Φ (a g) = ξ (c(a) ρ g v) = a^{iν} Φ(g)`.
- *Nonvanishing.* `Φ 1 = ξ v ≠ 0`.

## Provenance

The route is the one sketched in the Markdown of `AdelicCyclicDistributionVectorReduction`, after
Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023), proof of Lemma 7.10, and
Segal's theorem as quoted by Harish-Chandra, Trans. AMS 75 (1953), §11. Two points differ from the
classical presentation: the scalar action of `𝔷` is obtained from Schur's lemma with a formal
adjoint (`FormalAdjointCommutant`), using only bounded operators, and the action of the enveloping
algebra on smooth vectors is built from the Library's differentiation of smooth functions through
Hilbert matrix coefficients (`SmoothVectorEnvelopingAction`).
