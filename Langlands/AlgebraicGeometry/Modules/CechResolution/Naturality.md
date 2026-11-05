# Naturality of the Čech comparison in the module

This module shows that the identification of alternating Čech cohomology with
actual `R`-module cohomology, `cechCohomologyIso` from
`CechResolution.CohomologyIso`, is natural in the quasi-coherent module. As an
application it reduces an inclusion of kernels of maps on actual cohomology in a
positive degree to a statement about alternating Čech cocycles and coboundaries.

The module is an internal construction. It uses the sheafified Čech complex and
augmentation of `CechResolution.Basic` and `CechResolution.Complex`, the
comparison isomorphism `sectionsComplexIso` of `CechResolution.Comparison`, the
FLT presheaf cochains `OModulePresheaf.cochain` and differentials
`OModulePresheaf.d`, and the published naturality of comparison maps
`AcyclicResolution.resolutionComparison_naturality`. It assumes no cohomological
result beyond these imports. Worker 1665 wrote it for the proof of Stacks
Project Lemma 30.20.4(3) (tag 02OB), where it is used in a degree-wise kernel
argument.

## Maps of sheafified Čech complexes

Fix a scheme `X` and a morphism `φ : M ⟶ N` of `𝒪_X`-modules.

* `sheafOnMap φ W : sheafOn M W ⟶ sheafOn N W` applies to `φ` the restriction to
  the open `W` followed by the pushforward along the open immersion of `W`.
  `sheafOnMap_app` records that on an open `V` it is `φ` on the open of `X`
  written in Lean as `W.ι ''ᵁ (W.ι ⁻¹ᵁ V)`, the intersection `W ∩ V`.
* `res_sheafOnMap` proves that `sheafOnMap` commutes with the restriction maps
  `res M h : sheafOn M W ⟶ sheafOn M W'` for `W' ≤ W`. On sections both sides
  are `φ` followed by a restriction, so the proof is naturality of `φ`.
* `unit_sheafOnMap` proves `unit M W ≫ sheafOnMap φ W = φ ≫ unit N W`. This is
  naturality of the unit of the restriction/pushforward adjunction.

For an ordered affine cover `𝒰` of `X`:

* `cechTermMap φ 𝒰 p : cechTerm 𝒰 M p ⟶ cechTerm 𝒰 N p` is the biproduct map
  with components `sheafOnMap φ (𝒰.inter s)` over the strictly increasing tuples
  `s : 𝒰.Idx p`. `cechTermMap_π` records the components.
* `cechD_cechTermMap` proves that these maps commute with the alternating Čech
  differentials `cechD`. Composing with a projection, both sides become the same
  alternating sum over deleted entries, matched term by term with
  `res_sheafOnMap`.
* `cechComplexMap φ 𝒰 : cechComplex 𝒰 M ⟶ cechComplex 𝒰 N` is the resulting
  cochain map. `cechComplexMap_f` records its components.
* `augmentation_cechTermMap` proves the degree-zero square
  `augmentation 𝒰 M ≫ cechTermMap φ 𝒰 0 = φ ≫ augmentation 𝒰 N`, factor by
  factor, from `unit_sheafOnMap`. `cechAug_cechComplexMap` promotes it to the
  square of augmented complexes
  `cechAug 𝒰 M ≫ cechComplexMap φ 𝒰 = single₀.map φ ≫ cechAug 𝒰 N`.
* `toCochainFun_cechTermMap` proves that the global sections of
  `cechTermMap φ 𝒰 p` correspond to applying `φ` factor by factor on the chart
  intersections under the identification `toCochainFun` of
  `CechResolution.Comparison`.

## Maps of alternating Čech cochain complexes

Let `π : X ⟶ Spec R`.

* `ofModulesHom π φ` is `φ` regarded as a morphism of the FLT presheaves
  `OModulePresheaf.ofModules π M ⟶ OModulePresheaf.ofModules π N`.
  `ofModulesHom_app_apply` records that its sections map is `φ.app U`.
* `cochainMap π φ 𝒰 p` is the `R`-linear map of alternating Čech `p`-cochains
  `c ↦ (s ↦ φ (c s))`. `cochainMap_apply` records this formula, and
  `cochainMap_comp_d` proves that these maps commute with the Čech differentials
  `OModulePresheaf.d`, by naturality of `φ` under restriction to faces.
* `cechCochainMap π φ 𝒰 : cechCochainComplex π 𝒰 M ⟶ cechCochainComplex π 𝒰 N`
  is the resulting map of cochain complexes of `R`-modules.
  `cechCochainMap_f_apply` records its components. `cechCochainComplex_d`
  records that the differential of `cechCochainComplex π 𝒰 M` from degree `p` to
  degree `p + 1` is `ModuleCat.ofHom ((OModulePresheaf.ofModules π M).d 𝒰 p)`.
* `sectionsComplexIso_hom_naturality` and `sectionsComplexIso_inv_naturality`
  prove that the isomorphism `sectionsComplexIso π 𝒰 M` between the relative
  global sections of the sheafified Čech complex and `cechCochainComplex π 𝒰 M`
  intertwines `cechComplexMap φ 𝒰` with `cechCochainMap π φ 𝒰`. The first
  follows from `toCochainFun_cechTermMap` degreewise and elementwise; the second
  is formal from the first.

## Naturality of the comparison isomorphism

`cechCohomologyIso_hom_naturality` assumes `IsSeparated π` and that `M` and `N`
are quasi-coherent. It proves, for every degree `n`,

```text
homologyMap (cechCochainMap π φ 𝒰) n ≫ (cechCohomologyIso π 𝒰 N n).hom
  = (cechCohomologyIso π 𝒰 M n).hom ≫ (relativeCohomology π n).map φ.
```

By definition, `cechCohomologyIso π 𝒰 M n` is the homology of the inverse of
`sectionsComplexIso π 𝒰 M` followed by the comparison map
`resolutionComparison (relativeGlobalSections π) (cechAug 𝒰 M) n`, which is an
isomorphism because `cechAug 𝒰 M` is a quasi-isomorphism whose terms are acyclic.
The proof composes two squares. The first is the homology of
`sectionsComplexIso_inv_naturality`. The second is
`resolutionComparison_naturality`, applied to the map of augmented resolutions
given by `cechAug_cechComplexMap`. The Lean proof chains these squares with
explicit associativity steps instead of rewriting, because the two descriptions
of the intermediate homology objects agree only up to definitional unfolding.

## Kernels of maps on cohomology

Let `R` be a commutative ring and consider cochain complexes of `R`-modules
indexed by `ℕ`.

* `exists_toCycles_eq_of_homologyπ_eq_zero` proves that a `(p + 1)`-cycle whose
  homology class vanishes is the image of some `y` in degree `p` under
  `toCycles`. The proof uses exactness at the cycles of the short complex formed
  by `toCycles` and the homology projection, whose second map is the cokernel of
  the first.
* `ker_homologyMap_le` treats maps of cochain complexes `a : C ⟶ D` and
  `b : C ⟶ E` and a degree `p`. Assume that for every `z` in degree `p + 1` with
  `d z = 0`, if `a z` is a coboundary then `b z` is a coboundary. The lemma then
  proves that the kernel of `homologyMap a (p + 1)` is contained in the kernel of
  `homologyMap b (p + 1)`. The proof lifts a homology class to a cycle `c`. Its
  image under `a` has zero class, so `a c = d y` by the previous lemma. The
  hypothesis gives `b c = d y'`. Injectivity of the inclusion of cycles then
  shows that the class of `b c` vanishes.

`ker_relativeCohomology_map_le` is the geometric form. Assume that `π` is
separated, that `M`, `N` and `N'` are quasi-coherent, and that `a : M ⟶ N` and
`b : M ⟶ N'`. Fix `p`. The hypothesis concerns every alternating Čech
`(p + 1)`-cochain `z` of `M` with `d z = 0`: whenever
`cochainMap π a 𝒰 (p + 1) z` is a Čech coboundary of `N`, the cochain
`cochainMap π b 𝒰 (p + 1) z` is a Čech coboundary of `N'`. The conclusion is
that the kernel of `(relativeCohomology π (p + 1)).map a` is contained in the
kernel of `(relativeCohomology π (p + 1)).map b`. The proof applies
`ker_homologyMap_le` to `cechCochainMap π a 𝒰` and `cechCochainMap π b 𝒰`, using
`cechCochainComplex_d` to identify the differentials. It transports the
resulting inclusion along the isomorphisms `cechCohomologyIso` by
`cechCohomologyIso_hom_naturality`.
