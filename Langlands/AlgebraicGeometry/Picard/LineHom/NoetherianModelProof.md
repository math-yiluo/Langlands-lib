# Finite linear models of line-bundle Hom over a Noetherian affine base

Proof of the Library statement `Picard.LineHom.NoetherianModelStatement`
(module `Picard/LineHom/NoetherianModelStatement`): for a Noetherian ring `R`,
a proper flat morphism `p : Y ⟶ Spec R` and locally free sheaves of rank one
`L`, `M` on `Y`, the relative Hom presheaf
`CoherentSheaves.intrinsicModuleHomPresheaf p L M` on `Over (Spec R)` has a
finite linear model (`FiniteLinearEquations.HasModel`): it is isomorphic to the
solution presheaf `solutionsPresheaf a` of finitely many homogeneous linear
equations with coefficients in `R`.

## Declarations

Section `Model`. Data: `p : Y ⟶ Spec R`; an ordered affine cover `𝒰` of `Y`
(FLT `Scheme.OrderedAffineCover`); frames `e i` of `L` and `f i` of `M` on
`𝒰.U i` (`he`, `hf`) with transition functions `α`, `β` (`hα`, `hβ`, Library
`Picard/CocycleLineBundleFrame`); a linear map `d : C0 → C1` of `R`-modules with
maps `ψ0`, `ψ1` to the gauge complex `gaugeD p α β : GaugeC0 p 𝒰 → GaugeC1 p 𝒰`
of `GaugeComplex` such that `gaugeD ∘ ψ0 = ψ1 ∘ d` (`comm`); and bijections
`E S` from the kernel of `id_S ⊗ d` to the solutions `Solutions a S`, for every
`R`-algebra `S`, compatible with algebra maps (`hE`, the shape produced by
`exists_kernel_solutions_model` of `FreeKernel`). For a test `T` in
`Over (Spec R)`, write `q_T = pullback.snd T.hom p` and `S_T = Γ(T.left, ⊤)`
(an `R`-algebra by the Library `sectionsAlgebra`).

- `modelFamily … T x`: for a solution `x` over `S_T`, the family
  `tensorGauge0 p 𝒰 T ((id ⊗ ψ0) (E S_T)⁻¹ x)` (`TensorComparison`), with the
  proof that it is a gauge family (`IsGaugeFamily`) of the pulled-back
  transition functions `pullbackCocycle q_T α` and `pullbackCocycle q_T β`.
- `lTensor_map_pullSections`: `id ⊗ ψ0` commutes with `pullSections g ⊗ id`.
- `preimage_le_map_preimage`: for `g : T' ⟶ T`,
  `q_T' ⁻¹ᵁ U ≤ ((Over.pullback p).map g).left ⁻¹ᵁ (q_T ⁻¹ᵁ U)`.
- `modelFamily_naturality`: for `g : T' ⟶ T`, coordinate `i` of the family of
  `mapSolutions a (pullSections g) x` is the image under
  `((Over.pullback p).map g).left.appLE` of coordinate `i` of the family of `x`.
- `modelMap_naturality_down`: the same naturality for the morphisms
  `(pullbackFrameHomEquiv … q_T)⁻¹ (modelFamily … T x)` of `TestCoordinates`,
  stated with `Langlands.Scheme.Modules.transport` along
  `((Over.pullback p).map g).left`.
- `modelMap : solutionsPresheaf a ⟶ intrinsicModuleHomPresheaf p L M`: on `T`,
  a solution `x` goes to the morphism `q_T^* L ⟶ q_T^* M` whose frame
  coordinates are `modelFamily … T x`.
- `modelFamily_bijective`: if `p` is separated, `T.left` is affine, and
  `TwoChartCech.kerMapBaseChange d (gaugeD p α β) ψ0 ψ1 comm A` is bijective for
  every `R`-algebra `A` (`hbij`), then `modelFamily … T` is a bijection onto the
  gauge families.
- `hasModel_of_gaugeModel`: under the same hypotheses on `p` and `hbij`, and if
  `M` is quasi-coherent, `HasModel (intrinsicModuleHomPresheaf p L M)`.

Section `Frames`.

- `exists_frameCover₂`: two locally free sheaves of rank one on a quasi-compact
  scheme admit frames on every member of a common finite ordered affine cover.

Main theorem.

- `noetherianModel : NoetherianModelStatement.{u}`.

## Proof as implemented

`modelFamily` is a gauge family: by `pulledGaugeD_eq_zero_iff` it suffices that
`pulledGaugeD` vanishes on it; by `pulledGaugeD_tensorGauge0` this is
`tensorGauge1` of `(gaugeD ∘ ψ0)`-tensored, which by `comm` equals
`(ψ1 ∘ d)`-tensored applied to an element of the kernel of `id ⊗ d`, hence `0`.

`modelFamily_naturality`: by `hE`, `(E S_T')⁻¹` of the pulled-back solution is
`TensorKernel.mapKernel d (pullSections g)` of `(E S_T)⁻¹ x`; then
`lTensor_map_pullSections` and `tensorGauge0_naturality` give the claim.
`modelMap_naturality_down` follows from it through
`pullbackFrameHomEquiv_transport` (using the commutativity
`Over.w ((Over.pullback p).map g)`), and `modelMap`'s naturality combines it
with `intrinsicModuleHomPresheaf_map_down`.

`modelFamily_bijective`: Mathlib `LinearMap.baseChange_eq_ltensor` identifies
the kernels of `d.baseChange S` and `id ⊗ d`, and `ψ0.baseChange` with
`id ⊗ ψ0`. Injectivity: equal families give equal `(id ⊗ ψ0)`-images by
injectivity of `tensorGauge0` (`tensorGauge0_bijective`), so equal images
under `kerMapBaseChange`, so equal kernel elements by `hbij`, so equal
solutions. Surjectivity: a gauge family is a zero of `pulledGaugeD`, hence by
`tensorGauge0_ker_bijective` the image of some `w` in the kernel of
`id ⊗ gaugeD`; by `hbij`, `w = (id ⊗ ψ0) z` for some `z` in the kernel of
`id ⊗ d`, and the solution `E S_T z` maps to the given family.

`hasModel_of_gaugeModel`: the solution presheaf is an fppf sheaf, being
isomorphic (`solutionsPresheafIso`) to the functor of points of the Library
scheme `equationsScheme a`, which is a sheaf (`AlgebraicSpace.schemeSheaf`);
the Hom presheaf is an fppf sheaf by the Library `intrinsicModuleHomSheaf`
(which uses that `M` is quasi-coherent). On affine tests, `modelMap` is the
composite of `ULift` equivalences, `modelFamily_bijective` and the equivalence
`pullbackFrameHomEquiv`, hence bijective. So `modelMap` is an isomorphism by
`isIso_of_bijective_affine` of `AffineExtension`, and its inverse gives the
model.

`exists_frameCover₂`: the affine opens on which both `L` and `M` have frames
form a basis of the topology (by `exists_isFrameOn_of_isLocallyFreeRankOne`,
restriction of frames `IsFrameOn.map`/`mono`, and the basis of affine opens);
quasi-compactness gives a finite subfamily covering `Y`
(`Opens.IsBasis.exists_finite_of_isCompact`), ordered by a bijection with a
`Fin`.

`noetherianModel`: `Y` is quasi-compact since `p` is proper. Choose a cover by
`exists_frameCover₂` and frames `e`, `f` on it, with their transition functions
`frameCocycle` (`isTransition_frameCocycle`). `exists_gauge_model` of
`CechModel` (which uses that `R` is Noetherian and `p` proper and flat) gives a
two-term complex `G.d` of finite projective `R`-modules with maps to the gauge
complex that are bijective on kernels after every base change.
`exists_kernel_solutions_model` of `FreeKernel` gives the linear system `a` and
the bijections `E`. `M` is quasi-coherent (`IsLocallyFreeRankOne.isQuasicoherent`)
and proper morphisms are separated, so `hasModel_of_gaugeModel` applies.

The auxiliary declarations are internal to this proof; the theorem
`noetherianModel` proves the Library statement exactly.
