# Ext as right derived functors of Hom

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.DerivedPlus` (`mapExtendIso`),
`Langlands.Cohomology.LeftExactHomology` (`derivedNatTrans`) and
`Langlands.Cohomology.SmoothExt` (`SmoothExt.ext`, by Worker 13), and on
Mathlib's `Abelian.Ext`, Hom complexes (`CochainComplex.HomComplex`), right
derived functors (`Functor.rightDerived`) and injective resolutions.

Mathlib defines `Abelian.Ext X Y n` as morphisms `X ⟶ Y⟦n⟧` in the derived
category, with `X` and `Y` placed in degree zero. The classical definition,
used by Harris and by the Library module `Langlands.Cohomology.SmoothExt`, is
the `n`-th right derived functor of `Hom(X, -)` evaluated at `Y`. This module
proves that the two agree as abelian groups whenever `Y` has injective
resolutions, and specializes the comparison to smooth representations: there
`SmoothExt.ext R G V n` evaluated at `W` has the underlying group of Mathlib's
`Ext V W n`.

## Setting

`C` is an abelian category with objects in `Type u` and morphisms in
`Type v`. `HasExt.{w} C` is Mathlib's hypothesis that the groups
`Ext X Y n` exist in `Type w`; it is an explicit instance argument wherever
`Ext` occurs, with `w` arbitrary. `preadditiveCoyoneda.obj (op X)` is
Mathlib's functor `Hom(X, -) : C ⥤ AddCommGrpCat.{v}`, and for a ring `S` with
`Linear S C`, `(linearCoyoneda S C).obj (op X)` is `Hom(X, -)` with values in
`ModuleCat.{v} S`. For a functor `F`, `F.rightDerived n` is Mathlib's right
derived functor, computed from the injective resolutions chosen by
`HasInjectiveResolutions C`. For an injective resolution `R` of `Y`,
`R.cocomplex` is the resolving complex indexed by `ℕ`, and `R.cochainComplex`
is its extension by zero to a complex indexed by `ℤ`.

## Declarations

| Declaration | Statement |
| --- | --- |
| `coyonedaHomComplexIso X L` | For a cochain complex `L` indexed by `ℤ`, an isomorphism of complexes of abelian groups from `Hom(X, L)` (the functor `Hom(X, -)` applied termwise to `L`) to `HomComplex ((singleFunctor C 0).obj X) L`, the Hom complex from `X` placed in degree zero to `L`. |
| `coyonedaHomologyAddEquiv X L n` | The degree `n` cohomology of `Hom(X, L)` is additively equivalent to `CohomologyClass ((singleFunctor C 0).obj X) L n`. |
| `resolutionHomologyIso X R n` | For an injective resolution `R` of `Y` and `n : ℕ`, the degree `n` cohomology of `Hom(X, R.cochainComplex)` is isomorphic to the degree `n` cohomology of `Hom(X, R.cocomplex)`. |
| `extAddEquivHomology X R n` | For `HasExt.{w} C` and an injective resolution `R` of `Y`, `Ext X Y n ≃+` the degree `n` cohomology of `Hom(X, R.cocomplex)`. |
| `extAddEquivRightDerived X Y n` | For `HasExt.{w} C` and `HasInjectiveResolutions C`, `Ext X Y n ≃+ ((preadditiveCoyoneda.obj (op X)).rightDerived n).obj Y`. |
| `linearRightDerivedIso S X Y n` | The image under `forget₂ (ModuleCat S) AddCommGrpCat` of `(((linearCoyoneda S C).obj (op X)).rightDerived n).obj Y` is isomorphic to `((preadditiveCoyoneda.obj (op X)).rightDerived n).obj Y`. |
| `extAddEquivLinearRightDerived S X Y n` | `Ext X Y n ≃+ (((linearCoyoneda S C).obj (op X)).rightDerived n).obj Y`, an additive equivalence onto the underlying group of the module. |
| `hasExt_smoothRep R G` (theorem) | `HasExt.{u} (SmoothRep.{u, u, u} R G)`. |
| `smoothExtAddEquiv R G V W n` | For `HasExt.{w} (SmoothRep.{u, u, u} R G)`, `(SmoothExt.ext R G V n).obj W ≃+ Ext V W n`. |

## Proofs

- `coyonedaHomComplexIso`: in degree `n` the component is the inverse of
  Mathlib's `Cochain.fromSingleEquiv (zero_add n)`, an additive equivalence
  between cochains of degree `n` from `X` placed in degree zero to `L` and
  morphisms `X ⟶ L.X n`; it sends `f` to `Cochain.fromSingleMk f`. The
  components commute with the differentials by Mathlib's
  `Cochain.δ_fromSingleMk`: the differential of `Cochain.fromSingleMk f` is
  `Cochain.fromSingleMk (f ≫ L.d i j)`, which is the differential of
  `Hom(X, L)` applied to `f`. No sign appears.
- `coyonedaHomologyAddEquiv`: the map on cohomology of
  `coyonedaHomComplexIso X L`, followed by Mathlib's
  `HomComplex.homologyAddEquiv`, which identifies the cohomology of a Hom
  complex with its group of cohomology classes.
- `resolutionHomologyIso`: since `R.cochainComplex` is the extension of
  `R.cocomplex` along Mathlib's embedding `ComplexShape.embeddingUpNat` of `ℕ`
  into `ℤ`, the map on cohomology of the inverse of the Library's
  `DerivedPlus.mapExtendIso` (applying `Hom(X, -)` termwise commutes with
  extension by zero), followed by Mathlib's
  `HomologicalComplex.extendHomologyIso` (the cohomology of an extended complex
  in degree `n` is the cohomology of the original complex in degree `n`).
- `extAddEquivHomology`: Mathlib's
  `InjectiveResolution.extAddEquivCohomologyClass`, which identifies
  `Ext X Y n` with the group of cohomology classes of degree `n` from `X`
  placed in degree zero to `R.cochainComplex`, followed by the inverse of
  `coyonedaHomologyAddEquiv X R.cochainComplex n` and by
  `resolutionHomologyIso X R n`.
- `extAddEquivRightDerived`: `extAddEquivHomology` for the chosen resolution
  `injectiveResolution Y`, followed by the inverse of Mathlib's
  `InjectiveResolution.isoRightDerivedObj`, which computes the right derived
  functor from that resolution.
- `linearRightDerivedIso`: the composite of `Hom(X, -)` with values in
  `S`-modules and `forget₂ (ModuleCat S) AddCommGrpCat` is definitionally
  equal to `preadditiveCoyoneda.obj (op X)`, so no comparison isomorphism is
  needed there. The Library's
  `LeftExactHomology.derivedNatTrans Φ F n : (F ⋙ Φ).rightDerived n ⟶ F.rightDerived n ⋙ Φ`
  is an isomorphism when `Φ` preserves homology
  (`LeftExactHomology.isIso_derivedNatTrans`), and Mathlib's
  `forget₂ (ModuleCat S) AddCommGrpCat` preserves homology. The declaration is
  the inverse of the component at `Y` of this isomorphism for
  `Φ = forget₂ (ModuleCat S) AddCommGrpCat` and
  `F = (linearCoyoneda S C).obj (op X)`.
- `extAddEquivLinearRightDerived`: `extAddEquivRightDerived` followed by the
  inverse of `linearRightDerivedIso`.
- `hasExt_smoothRep`: Mathlib's `hasExt_of_enoughInjectives` at universe `u`,
  using that `SmoothRep.{u, u, u} R G` has enough injectives (Library module
  `Representation/Category/SmoothPartAdjunction`) and morphisms in `Type u`.
- `smoothExtAddEquiv`: `SmoothExt.ext R G V n` is by definition the right
  derived functor of `SmoothHomComplex.homFunctor R G V`, which is
  `(linearCoyoneda R (SmoothRep R G)).obj (op V)`; the declaration is the
  inverse of `extAddEquivLinearRightDerived R V W n`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`). Proposition
4.4, equation (4.4.1), printed p.309 (one-based PDF page 11): "Here `Ext^i`
denotes the `i`-th derived functor of `Hom` in the category of smooth
`O_m[GJ]`-modules." Proposition 4.10, printed p.311 (one-based PDF page 13),
uses the same convention for smooth `L_ℓ[GJ]`-modules in the spectral sequence
(4.10.1). Both passages were read by Worker 61 in the rendered page scans.

Harris's `Ext` is therefore the classical one, which the Library realizes as
`Langlands.Cohomology.SmoothExt.ext` (right derived functors of equivariant
Hom in the second variable). Spectral sequences built from Mathlib's derived
categories produce Mathlib's `Abelian.Ext` instead. This module supplies the
comparison: `smoothExtAddEquiv` says that, for smooth representations with
coefficient ring and group in one universe `u`, the two agree as abelian
groups. The comparison is classical; the statements and proofs here are ours,
assembled from Mathlib and the Library. Harris works with coefficient rings
`O_m = O/λ^m O` and with `L_ℓ`; this module treats any commutative ring
`R` and any topological group `G` in universe `u`, and no Harris-specific
ring or group is introduced.

## Scope

- All comparisons are additive equivalences or isomorphisms of abelian groups.
  Mathlib gives `Ext X Y n` an `S`-module structure when `C` is `S`-linear
  (`Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear`, not imported here),
  and `SmoothExt.ext` takes values in `R`-modules; the equivalences are not
  shown to be `S`-linear (respectively `R`-linear).
- No naturality in `X` or `Y`, no compatibility with composition (Yoneda
  products) and no compatibility with the connecting maps of long exact
  sequences is stated.
- `hasExt_smoothRep` is a theorem, not an instance, following Mathlib's
  convention for `hasExt_of_enoughInjectives`; `smoothExtAddEquiv` takes
  `HasExt.{w}` for an arbitrary universe `w` as an instance argument.
- Smooth representations are those of `SmoothRep.{u, u, u} R G`, with the
  ring, the group and the representation carriers in one universe `u`, as in
  `Langlands.Cohomology.SmoothExt`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.309 and 311 read in the rendered page scans.

Dependencies: `Langlands.Cohomology.DerivedPlus`,
`Langlands.Cohomology.LeftExactHomology`, `Langlands.Cohomology.SmoothExt`
and Mathlib (`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`,
`Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives`,
`Mathlib.CategoryTheory.Abelian.Injective.Ext`,
`Mathlib.CategoryTheory.Linear.Yoneda`), pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
