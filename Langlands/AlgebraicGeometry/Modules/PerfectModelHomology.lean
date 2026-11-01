import Langlands.AlgebraicGeometry.Modules.PerfectModelRestriction
import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChangeZero
import Langlands.Cohomology.ModuleComplex.BaseChangeHomology

/-!
# Perfect models and cohomology base change maps

Let `L` be a line bundle on `X`, `f : X ⟶ Spec R`, `K` a strictly perfect complex of
`R`-modules with a derived morphism `a : K ⟶ RΓ_R(X, L)`, and `hp : IsPullback p f' f (Spec.map φ)`
a pullback square with `φ : R ⟶ T`. Write `c_n : T ⊗_R H^n(K) ⟶ H^n(T ⊗_R K)` for the comparison
`ModuleComplex.baseChangeDerivedHomologyMap`.

On `H^n`, the base-changed model `perfectModelBaseChange hp L hK a : T ⊗_R K ⟶ RΓ_T(X', p^* L)`
composed with `c_n` is the scalar extension of `H^n(a)` followed by the `T`-linear cohomology
base-change map `scalarBaseChangeMap` (`perfectModelBaseChange_homology`). In degree zero the same
holds for the base-change map on relative sections `scalarSectionsBaseChangeMap`
(`perfectModelBaseChange_homology_zero`).

Hence, if `a` and `perfectModelBaseChange hp L hK a` are isomorphisms, the cohomology base-change
map in degree `n` is an isomorphism exactly when `c_n` is
(`isIso_scalarBaseChangeMap_iff_of_perfectModel`, `isIso_scalarSectionsBaseChangeMap_iff_of_perfectModel`).
This holds in particular when `K` vanishes in degree `n + 1`
(`isIso_scalarBaseChangeMap_of_perfectModel_of_isZero`,
`isIso_scalarSectionsBaseChangeMap_of_perfectModel_of_isZero`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

variable {X X' : Scheme.{u}} {R T : CommRingCat.{u}} {φ : R ⟶ T} {f : X ⟶ Spec R}
  {f' : X' ⟶ Spec T} {p : X' ⟶ X} (hp : IsPullback p f' f (Spec.map φ))

/-- On `H^n`, the comparison `T ⊗_R H^n(K) ⟶ H^n(T ⊗_R K)` followed by the base-changed perfect
model is the scalar extension of `H^n(a)` followed by the `T`-linear cohomology base-change map,
through the identifications `H^n(RΓ(-)) ≅ H^n(-)`. -/
theorem perfectModelBaseChange_homology (L : LineBundle X)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (a : DerivedCategory.Q.obj K ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        L.obj) (n : ℕ) :
    ModuleComplex.baseChangeDerivedHomologyMap φ.hom K n ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} T) n).map
          (perfectModelBaseChange hp L hK a) ≫
        (DerivedPlus.homologyIso (relativeGlobalSections f')
          (injectiveResolution ((Scheme.Modules.pullback p).obj L.obj)) n).hom =
      (ModuleCat.extendScalars φ.hom).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map a ≫
            (DerivedPlus.homologyIso (relativeGlobalSections f)
              (injectiveResolution L.obj) n).hom) ≫
        scalarBaseChangeMap φ f f' p hp.w L.obj
          (isZero_higherDirectImage_pullback_lineBundle_of_isPullback hp L) n := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right,
    ModuleComplex.homEquiv_baseChangeDerivedHomologyMap_comp φ.hom K n hK,
    perfectScalarDerivedTargetHomEquiv_perfectModelBaseChange,
    Adjunction.homEquiv_naturality_left]
  erw [scalarBaseChangeMap_homEquiv φ f f' p hp.w L.obj _
      (fun J hJ q => (pushforwardInjectiveAcyclic X' X p J hJ q).2 R f)]
  simp only [derivedBaseChangeMapLineBundle, Functor.map_comp, Category.assoc]
  rw [derivedBaseChangeMap_homology]

/-- In degree zero, the comparison `T ⊗_R H^0(K) ⟶ H^0(T ⊗_R K)` followed by the base-changed
perfect model is the scalar extension of `H^0(a)` followed by the `T`-linear base-change map on
relative sections, through the identifications `H^0(RΓ(-)) ≅ Γ(-)`. -/
theorem perfectModelBaseChange_homology_zero (L : LineBundle X)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (a : DerivedCategory.Q.obj K ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        L.obj) :
    ModuleComplex.baseChangeDerivedHomologyMap φ.hom K ((0 : ℕ) : ℤ) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} T) ((0 : ℕ) : ℤ)).map
          (perfectModelBaseChange hp L hK a) ≫
        (DerivedPlus.homologyIso (relativeGlobalSections f')
          (injectiveResolution ((Scheme.Modules.pullback p).obj L.obj)) 0).hom ≫
        (relativeCohomologyZeroIso f').hom.app ((Scheme.Modules.pullback p).obj L.obj) =
      (ModuleCat.extendScalars φ.hom).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ((0 : ℕ) : ℤ)).map a ≫
            (DerivedPlus.homologyIso (relativeGlobalSections f)
              (injectiveResolution L.obj) 0).hom ≫
            (relativeCohomologyZeroIso f).hom.app L.obj) ≫
        scalarSectionsBaseChangeMap φ f f' p hp.w L.obj := by
  rw [reassoc_of% perfectModelBaseChange_homology hp L hK a 0, scalarBaseChangeMap_zero]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- If `a` and its base change `perfectModelBaseChange hp L hK a` are isomorphisms, then the
`T`-linear cohomology base-change map in degree `n` is an isomorphism exactly when the comparison
`T ⊗_R H^n(K) ⟶ H^n(T ⊗_R K)` is. -/
theorem isIso_scalarBaseChangeMap_iff_of_perfectModel (L : LineBundle X)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (a : DerivedCategory.Q.obj K ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        L.obj) (n : ℕ) (ha : IsIso a) (hb : IsIso (perfectModelBaseChange hp L hK a)) :
    IsIso (scalarBaseChangeMap φ f f' p hp.w L.obj
        (isZero_higherDirectImage_pullback_lineBundle_of_isPullback hp L) n) ↔
      IsIso (ModuleComplex.baseChangeDerivedHomologyMap φ.hom K n) := by
  have h := perfectModelBaseChange_homology hp L hK a n
  constructor
  · intro hs
    have : IsIso (ModuleComplex.baseChangeDerivedHomologyMap φ.hom K n ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} T) n).map
          (perfectModelBaseChange hp L hK a) ≫
        (DerivedPlus.homologyIso (relativeGlobalSections f')
          (injectiveResolution ((Scheme.Modules.pullback p).obj L.obj)) n).hom) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right (ModuleComplex.baseChangeDerivedHomologyMap φ.hom K n)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) n).map
          (perfectModelBaseChange hp L hK a) ≫
        (DerivedPlus.homologyIso (relativeGlobalSections f')
          (injectiveResolution ((Scheme.Modules.pullback p).obj L.obj)) n).hom)
  · intro hc
    have : IsIso ((ModuleCat.extendScalars φ.hom).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map a ≫
            (DerivedPlus.homologyIso (relativeGlobalSections f)
              (injectiveResolution L.obj) n).hom) ≫
        scalarBaseChangeMap φ f f' p hp.w L.obj
          (isZero_higherDirectImage_pullback_lineBundle_of_isPullback hp L) n) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_left ((ModuleCat.extendScalars φ.hom).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map a ≫
            (DerivedPlus.homologyIso (relativeGlobalSections f)
              (injectiveResolution L.obj) n).hom))
      (scalarBaseChangeMap φ f f' p hp.w L.obj
        (isZero_higherDirectImage_pullback_lineBundle_of_isPullback hp L) n)

/-- If `a` and `perfectModelBaseChange hp L hK a` are isomorphisms and `K` vanishes in degree
`n + 1`, then the `T`-linear cohomology base-change map in degree `n` is an isomorphism. -/
theorem isIso_scalarBaseChangeMap_of_perfectModel_of_isZero (L : LineBundle X)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (a : DerivedCategory.Q.obj K ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        L.obj) (n : ℕ) (ha : IsIso a) (hb : IsIso (perfectModelBaseChange hp L hK a))
    (hK1 : IsZero (K.X ((n : ℤ) + 1))) :
    IsIso (scalarBaseChangeMap φ f f' p hp.w L.obj
      (isZero_higherDirectImage_pullback_lineBundle_of_isPullback hp L) n) :=
  (isIso_scalarBaseChangeMap_iff_of_perfectModel hp L hK a n ha hb).2
    (ModuleComplex.isIso_baseChangeDerivedHomologyMap_of_isZero φ.hom K n hK1)

/-- If `a` and `perfectModelBaseChange hp L hK a` are isomorphisms, then the `T`-linear
base-change map on relative sections `T ⊗_R Γ(X, L) ⟶ Γ(X', p^* L)` is an isomorphism exactly
when the comparison `T ⊗_R H^0(K) ⟶ H^0(T ⊗_R K)` is. -/
theorem isIso_scalarSectionsBaseChangeMap_iff_of_perfectModel (L : LineBundle X)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (a : DerivedCategory.Q.obj K ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        L.obj) (ha : IsIso a) (hb : IsIso (perfectModelBaseChange hp L hK a)) :
    IsIso (scalarSectionsBaseChangeMap φ f f' p hp.w L.obj) ↔
      IsIso (ModuleComplex.baseChangeDerivedHomologyMap φ.hom K ((0 : ℕ) : ℤ)) := by
  rw [← isIso_scalarBaseChangeMap_iff_of_perfectModel hp L hK a 0 ha hb,
    scalarBaseChangeMap_zero]
  constructor
  · intro hs
    infer_instance
  · intro hs
    have : IsIso (scalarSectionsBaseChangeMap φ f f' p hp.w L.obj ≫
        (relativeCohomologyZeroIso f').inv.app ((Scheme.Modules.pullback p).obj L.obj)) :=
      IsIso.of_isIso_comp_left ((ModuleCat.extendScalars φ.hom).map
        ((relativeCohomologyZeroIso f).hom.app L.obj)) _
    exact IsIso.of_isIso_comp_right (scalarSectionsBaseChangeMap φ f f' p hp.w L.obj)
      ((relativeCohomologyZeroIso f').inv.app ((Scheme.Modules.pullback p).obj L.obj))

/-- If `a` and `perfectModelBaseChange hp L hK a` are isomorphisms and `K` vanishes in degree
`1`, then the `T`-linear base-change map on relative sections `T ⊗_R Γ(X, L) ⟶ Γ(X', p^* L)` is
an isomorphism. -/
theorem isIso_scalarSectionsBaseChangeMap_of_perfectModel_of_isZero (L : LineBundle X)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (a : DerivedCategory.Q.obj K ⟶
      (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj
        L.obj) (ha : IsIso a) (hb : IsIso (perfectModelBaseChange hp L hK a))
    (hK1 : IsZero (K.X 1)) :
    IsIso (scalarSectionsBaseChangeMap φ f f' p hp.w L.obj) :=
  (isIso_scalarSectionsBaseChangeMap_iff_of_perfectModel hp L hK a ha hb).2
    (ModuleComplex.isIso_baseChangeDerivedHomologyMap_of_isZero φ.hom K _ hK1)

end Langlands.AlgebraicGeometry.Modules.DerivedSections
