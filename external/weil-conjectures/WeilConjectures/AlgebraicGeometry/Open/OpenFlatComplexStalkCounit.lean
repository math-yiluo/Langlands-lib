/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import all WeilConjectures.Algebra.Homology.StalkKFlatTensorHomology
import all WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import all WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.Single
import all WeilConjectures.Algebra.Homology.TensorRestrictExtendScalars
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import all WeilConjectures.Algebra.Homology.StalkTensorComplex
import all WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all Mathlib.CategoryTheory.Adjunction.FullyFaithful
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Topology.Sheaves.Abelian
import all WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso

/-! # Local comparison factors

## References

* Stacks Project, Tags 0DJ7 and 0DJ9
* Tags 06YB and 0D5S
* Stacks Project, Tag 06Y6
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Compatible ring isomorphisms identify ordinary scalar extension on complexes. -/
private theorem extensionComplexIso
    {S₀ S D₀ D : Type u}
    [CommRing S₀] [CommRing S] [CommRing D₀] [CommRing D]
    (f₀ : S₀ →+* D₀) (f : S →+* D)
    (eS : S₀ ≃+* S) (eD : D₀ ≃+* D)
    (hf : eD.toRingHom.comp f₀ = f.comp eS.toRingHom)
    (Q₀ : CochainComplex (ModuleCat.{u} S₀) ℤ)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ)
    (q : Q₀ ≅ ((ModuleCat.restrictScalars eS.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj Q) :
    Nonempty (((ModuleCat.extendScalars f₀).mapHomologicalComplex (.up ℤ)).obj Q₀ ≅
      ((ModuleCat.restrictScalars eD.toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q)) := by
  let ES := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u} eS
  let ED := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u} eD
  have hf' : f₀.comp eS.symm.toRingHom = eD.symm.toRingHom.comp f := by
    ext r
    apply eD.injective
    simpa using RingHom.congr_fun hf (eS.symm r)
  let a := ES.toAdjunction.comp (ModuleCat.extendRestrictScalarsAdj f₀)
  let b := (ModuleCat.extendRestrictScalarsAdj f).comp ED.toAdjunction
  let t := (ModuleCat.restrictScalarsComp eS.symm.toRingHom f₀).symm ≪≫
    ModuleCat.restrictScalarsComp' f eD.symm.toRingHom
      (f₀.comp eS.symm.toRingHom) hf'
  let c := (conjugateIsoEquiv b a).symm t.symm
  exact ⟨((ModuleCat.extendScalars f₀).mapHomologicalComplex (.up ℤ)).mapIso q ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app Q ≪≫
    (NatIso.mapHomologicalComplex c (.up ℤ)).app Q ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm.app Q⟩

private theorem tensorStalkIsoAt
    [∀ Y : Scheme.{u},
      HasDerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {Y X : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    Nonempty
      ((((ModuleCat.extendScalars
        ((Y.presheaf.stalkCongr (.of_eq h)).inv ≫ f.stalkMap x).hom).mapHomologicalComplex
          (.up ℤ)).obj
        (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
          (.up ℤ)).obj K)) ≅
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (.up ℤ)).obj (((Scheme.Modules.tensorPullback f).mapHomologicalComplex
          (.up ℤ)).obj K))) := by
  subst y
  let := stalk_additive Y.toRingedSpace (f x)
  let := stalk_additive X.toRingedSpace x
  let : (Scheme.Modules.tensorPullback f).Additive :=
    SingleComplexBaseChange.tensorPullbackAdditive f
  obtain ⟨t, _⟩ := Scheme.Modules.exists_tensorPullback_stalk_iso f x
  simp only [TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  exact ⟨(Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app K ≪≫
    (NatIso.mapHomologicalComplex t.symm (.up ℤ)).app K ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm.app K⟩

set_option linter.unusedVariables false in
/-- The stalk scalar-extension counit computes the local sheaf pullback counit
on a bounded-above flat sheaf complex, including transport of both local rings. -/
theorem openFlatComplex_stalk_counit
    {B A : Scheme.{u}} (g : A ⟶ B) (a : A)
    (S : B.Opens) (V : A.Opens) (hS : g a ∈ S) (hV : a ∈ V)
    (hVS : V ≤ g ⁻¹ᵁ S)
    (K : CochainComplex (SheafOfModules.{u}
      (moduleRings S.toScheme.toRingedSpace)) ℤ)
    (hbound : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    let T := A.presheaf.stalk a
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} T)
    let xS : S.toScheme := ⟨g a, hS⟩
    let xV : V.toScheme := ⟨a, hV⟩
    let P := ((ModuleCat.restrictScalars
      (S.stalkIso xS).inv.hom).mapHomologicalComplex (.up ℤ)).obj
      (((RingedSpace.moduleStalkFunctor S.toScheme.toRingedSpace xS).mapHomologicalComplex
         (.up ℤ)).obj K)
    let F := RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace xV ⋙
      ModuleCat.restrictScalars (V.stalkIso xV).inv.hom
    let j := g.resLE S V hVS
    let qK := (HomotopyCategory.quotient _ (.up ℤ)).obj K
    ∀ (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh)
      (hLF : LF.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))) (n : ℤ),
      ∃ (l : F.obj ((DerivedCategory.homologyFunctor _ n).obj
            ((derivedPullback j).obj (DerivedCategory.Qh.obj qK))) ≅
          (DerivedCategory.homologyFunctor _ n).obj
            (LF.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))))
        (r : (DerivedCategory.homologyFunctor _ n).obj
            (DerivedCategory.Qh.obj
              (((ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory
                (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≅
          F.obj ((DerivedCategory.homologyFunctor _ n).obj
            (DerivedCategory.Qh.obj
              (((Scheme.Modules.tensorPullback j).mapHomotopyCategory (.up ℤ)).obj qK)))),
        F.map ((DerivedCategory.homologyFunctor _ n).map
            ((SingleComplexBaseChange.counit j).app qK)) =
          l.hom ≫ (DerivedCategory.homologyFunctor _ n).map
            (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ r.hom := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let R := B.presheaf.stalk (g a)
  let T := A.presheaf.stalk a
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} T)
  let xS : S.toScheme := ⟨g a, hS⟩
  let xV : V.toScheme := ⟨a, hV⟩
  let j := g.resLE S V hVS
  let U := ModuleCat.restrictScalars (S.stalkIso xS).inv.hom
  let W := ModuleCat.restrictScalars (V.stalkIso xV).inv.hom
  let Z := RingedSpace.moduleStalkFunctor S.toScheme.toRingedSpace xS
  let F := RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace xV ⋙ W
  let Q := (Z.mapHomologicalComplex (.up ℤ)).obj K
  let P := (U.mapHomologicalComplex (.up ℤ)).obj Q
  let qK := (HomotopyCategory.quotient _ (.up ℤ)).obj K
  dsimp only
  intro LF ε hLF n
  have hK := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    S.toScheme.toRingedSpace K hbound hflat
  have hc := SingleComplexBaseChange.counit_isIso_of_isKFlat j K hK
  let := hc
  have hQ := (RingedSpace.isKFlat_iff_stalk_isKFlat
    S.toScheme.toRingedSpace K).mp hK xS
  have hP := ringIso_kFlat (S.stalkIso xS).symm.commRingCatIsoToRingEquiv Q hQ
  have : (ModuleCat.extendScalars (g.stalkMap a).hom).PreservesKFlatQuasiIso :=
    ⟨fun hL hM f ↦ CochainComplex.scalarExtension_quasiIso_of_kFlat
      (g.stalkMap a).hom f (show QuasiIso f from inferInstance) hL hM⟩
  let := (Functor.isLeftDerivedFunctor_iff_isIso_app_of_kFlat
    (ModuleCat.extendScalars (g.stalkMap a).hom) ε).1 hLF P
      hP
  have hx : j xV = xS := by
    apply Subtype.ext
    simp [j, xV, xS]
  let jmap : S.toScheme.presheaf.stalk xS ⟶ V.toScheme.presheaf.stalk xV :=
    (S.toScheme.presheaf.stalkCongr (.of_eq hx)).inv ≫ j.stalkMap xV
  have hf : (V.stalkIso xV).inv.hom.comp (g.stalkMap a).hom =
      jmap.hom.comp (S.stalkIso xS).inv.hom := by
    have hh := Arrow.iso_w (g.resLEStalkMap hVS xV)
    have hh' := congrArg (fun z ↦ z ≫ (V.stalkIso xV).inv) hh
    simp only [Scheme.Hom.resLEStalkMap, Arrow.isoMk_inv_left,
      Arrow.isoMk_hom_right, Iso.trans_inv, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at hh'
    have hp := S.ι.stalkMap_congr_point (j xV) xS hx
    rw [← Scheme.Opens.stalkIso_inv, ← Scheme.Opens.stalkIso_inv] at hp
    have hp' := congrArg (fun z ↦
      (B.presheaf.stalkCongr (.of_eq (congrArg Subtype.val hx))).inv ≫ z ≫
        (S.toScheme.presheaf.stalkCongr (.of_eq hx)).inv) hp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] at hp'
    change (g.stalkMap a ≫ (V.stalkIso xV).inv).hom =
      ((S.stalkIso xS).inv ≫ jmap).hom
    apply congrArg CommRingCat.Hom.hom
    erw [hh']
    dsimp only [jmap]
    erw [← Category.assoc, hp']
    rfl
  obtain ⟨s⟩ := extensionComplexIso
    (g.stalkMap a).hom jmap.hom
    (S.stalkIso xS).symm.commRingCatIsoToRingEquiv
    (V.stalkIso xV).symm.commRingCatIsoToRingEquiv hf P Q (Iso.refl _)
  let := stalk_additive V.toScheme.toRingedSpace xV
  let := stalk_preservesHomology V.toScheme.toRingedSpace xV
  let : PreservesFiniteLimits (RingedSpace.moduleStalkFunctor
      V.toScheme.toRingedSpace xV) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : PreservesFiniteColimits (RingedSpace.moduleStalkFunctor
      V.toScheme.toRingedSpace xV) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  let : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  obtain ⟨t'⟩ := tensorStalkIsoAt j xV xS hx K
  let ordinary := s ≪≫ (W.mapHomologicalComplex (.up ℤ)).mapIso t'
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} T) n
  let D := ((ModuleCat.extendScalars (g.stalkMap a).hom).mapHomologicalComplex
    (.up ℤ)).obj P
  let : HasDerivedCategory V.toScheme.Modules :=
    HasDerivedCategory.standard V.toScheme.Modules
  let C := ((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj K
  let r := H.mapIso (DerivedCategory.Qh.mapIso
      (((ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategoryFactors
        (.up ℤ)).app P)) ≪≫
    H.mapIso ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} T)).app D) ≪≫
    H.mapIso (DerivedCategory.Q.mapIso ordinary) ≪≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} T) n).app
      ((F.mapHomologicalComplex (.up ℤ)).obj C)) ≪≫
    (F.mapHomologicalComplexHomologyIso (.up ℤ) n).app
      (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj K) ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors _ n).symm.app C) ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor _ n).mapIso
      ((DerivedCategory.quotientCompQhIso _).symm.app C))
  let c := F.mapIso ((DerivedCategory.homologyFunctor _ n).mapIso
    (asIso ((SingleComplexBaseChange.counit j).app qK)))
  let e := H.mapIso (asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
  refine ⟨c ≪≫ r.symm ≪≫ e.symm, r, ?_⟩
  change c.hom = (c ≪≫ r.symm ≪≫ e.symm).hom ≫ e.hom ≫ r.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry
