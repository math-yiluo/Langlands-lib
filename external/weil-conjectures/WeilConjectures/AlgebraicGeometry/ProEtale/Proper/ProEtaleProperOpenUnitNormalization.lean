/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek

import all WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedClosureComparisonSquare
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenIdentificationNormalization
import all WeilConjectures.AlgebraicGeometry.UnboundedDirectImageBoundedBelow

/-! # Open-unit normalization before finite coefficient realization

## References

* Stacks 03DI, 03D6, 0F7B
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
attribute [local implicit_reducible] AlgebraicGeometry.Etale.rightDerivedLowerStarPlus
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

private theorem transport_normalization
    {C D T C' D' T' : Type*}
    [Category C] [Category D] [Category T]
    [Category C'] [Category D'] [Category T']
    {J₁ : C ⥤ D} {J₂ : C ⥤ T} {U₁ : D ⥤ C} {U₂ : T ⥤ C}
    {J₁' : C' ⥤ D'} {J₂' : C' ⥤ T'} {U₁' : D' ⥤ C'} {U₂' : T' ⥤ C'}
    (a₁ : J₁ ⊣ U₁) (a₂ : J₂ ⊣ U₂) (b₁ : J₁' ⊣ U₁') (b₂ : J₂' ⊣ U₂')
    (P : D ⥤ T) (P' : D' ⥤ T') (Q : C ⥤ C') (Q₁ : D ⥤ D') (Q₂ : T ⥤ T')
    (ρ : P ⋙ U₂ ⟶ U₁) (ρ' : P' ⋙ U₂' ⟶ U₁')
    (v₁ : Q₁ ⋙ U₁' ≅ U₁ ⋙ Q) (v₂ : Q₂ ⋙ U₂' ≅ U₂ ⋙ Q)
    (χ : P ⋙ Q₂ ⟶ Q₁ ⋙ P')
    (hχ : ∀ N, U₂'.map (χ.app N) ≫ ρ'.app (Q₁.obj N) ≫ v₁.hom.app N =
      v₂.hom.app (P.obj N) ≫ Q.map (ρ.app N))
    (K : C) (m : J₂.obj K ⟶ P.obj (J₁.obj K))
    (o₁ : Q₁.obj (J₁.obj K) ≅ J₁'.obj (Q.obj K))
    (o₂ : Q₂.obj (J₂.obj K) ≅ J₂'.obj (Q.obj K))
    (hu₁ : b₁.unit.app (Q.obj K) ≫ U₁'.map o₁.inv =
      Q.map (a₁.unit.app K) ≫ v₁.inv.app (J₁.obj K))
    (hu₂ : b₂.unit.app (Q.obj K) ≫ U₂'.map o₂.inv =
      Q.map (a₂.unit.app K) ≫ v₂.inv.app (J₂.obj K))
    (hm : a₂.homEquiv _ _ m ≫ ρ.app (J₁.obj K) = a₁.unit.app K) :
    b₂.homEquiv _ _ (o₂.inv ≫ Q₂.map m ≫ χ.app (J₁.obj K) ≫ P'.map o₁.hom) ≫
      ρ'.app (J₁'.obj (Q.obj K)) = b₁.unit.app (Q.obj K) := by
  have hr : U₂'.map (χ.app (J₁.obj K)) ≫ ρ'.app (Q₁.obj (J₁.obj K)) =
      v₂.hom.app (P.obj (J₁.obj K)) ≫ Q.map (ρ.app (J₁.obj K)) ≫
        v₁.inv.app (J₁.obj K) := by
    simpa only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id, Category.id_comp] using
      congrArg (fun z ↦ z ≫ v₁.inv.app (J₁.obj K)) (hχ (J₁.obj K))
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] at hm ⊢
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hu₂]
  simp only [Category.assoc]
  have hn := ρ'.naturality o₁.hom
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [reassoc_of% hr, ← reassoc_of% v₂.inv.naturality m]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Q.map_comp_assoc, ← Q.map_comp_assoc, Category.assoc, hm]
  rw [← reassoc_of% hu₁, ← U₁'.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- Restriction along an open triangle is inverse-image composition followed by
restriction of the proper counit. This construction does not require properness. -/
def properOpenRestriction (A : Type (u + 1)) [CommRing A]
    {X T₁ T₂ : Scheme.{u}} (r : T₁ ⟶ T₂)
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ r = j₂) :
    (lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor ⋙
        (upperStar (ModuleCat.{u + 1} A) j₂).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) j₁).mapDerivedCategory :=
  let k := Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} A)) h.symm) ≪≫
        upperStarComp (ModuleCat.{u + 1} A) j₁ r) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  { app N := k.hom.app _ ≫
      (upperStar (ModuleCat.{u + 1} A) j₁).mapDerivedCategory.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r
        ).mapDerivedCategoryRightDerivedAdjunction.counit.app N)
    naturality {M N} a := by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [reassoc_of% k.hom.naturality
        ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor.map a)]
      rw [← Functor.map_comp, Adjunction.counit_naturality, Functor.map_comp]
      exact (Category.assoc _ _ _).symm }

private def restrictionPlus (A : Type (u + 1)) [CommRing A]
    {X T₁ T₂ : Scheme.{u}} (r : T₁ ⟶ T₂)
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ r = j₂) :
    (lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlus ⋙
        (upperStar (ModuleCat.{u + 1} A) j₂).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) j₁).mapDerivedCategoryPlus :=
  let k := closureSquareProEtalePullComp A j₁ r j₂ h
  { app N := k.hom.app _ ≫
      (upperStar (ModuleCat.{u + 1} A) j₁).mapDerivedCategoryPlus.map
        ((derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} A) r).counit.app N)
    naturality {M N} a := by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [reassoc_of% k.hom.naturality
        ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlus.map a)]
      rw [← Functor.map_comp, Adjunction.counit_naturality, Functor.map_comp]
      exact (Category.assoc _ _ _).symm }

set_option backward.defeqAttrib.useBackward true in
private theorem plus_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T₁ T₂ : Scheme.{u}} (r : T₁ ⟶ T₂) [IsProper r]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ r = j₂)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} A) j₂).homEquiv _ _
        (properOpenProEtaleIsoPlus A r j₁ j₂ h L).hom ≫
      (restrictionPlus A r j₁ j₂ h).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)) =
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} A) j₁).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L) := by
  let B := ModuleCat.{u + 1} A
  let Q := (comparisonUpperStar B X).mapDerivedCategoryPlus
  let Q₁ := (comparisonUpperStar B T₁).mapDerivedCategoryPlus
  let Q₂ := (comparisonUpperStar B T₂).mapDerivedCategoryPlus
  let U₁ := (Etale.upperStar B j₁).mapDerivedCategoryPlus
  let U₂ := (Etale.upperStar B j₂).mapDerivedCategoryPlus
  let U₁' := (upperStar B j₁).mapDerivedCategoryPlus
  let U₂' := (upperStar B j₂).mapDerivedCategoryPlus
  let a := Etale.derivedUpperStarLowerStarAdjunctionPlus B r
  let b := derivedUpperStarLowerStarAdjunctionPlus B r
  let k := Etale.upperStarCompDerivedPlus B j₁ r j₂ h.symm
  let k' := closureSquareProEtalePullComp A j₁ r j₂ h
  let v₁ := (fixedComparisonPullbackPlus A j₁).symm
  let v₂ := (fixedComparisonPullbackPlus A j₂).symm
  let v := (fixedComparisonPullbackPlus A r).symm
  let χ := fixedComparisonDirectImageMatePlus A r
  let ρ : ((Etale.lowerStar B r).rightDerivedFunctorPlus) ⋙ U₂ ⟶ U₁ :=
    { app N := k.hom.app _ ≫ U₁.map (a.counit.app N)
      naturality {M N} z := by
        dsimp only [Functor.comp_obj, Functor.comp_map]
        rw [reassoc_of% k.hom.naturality (((Etale.lowerStar B r).rightDerivedFunctorPlus).map z)]
        rw [← Functor.map_comp, Adjunction.counit_naturality, Functor.map_comp]
        exact (Category.assoc _ _ _).symm }
  have hc (N) : ((upperStar B r).mapDerivedCategoryPlus).map (χ.app N) ≫
      b.counit.app (Q₁.obj N) =
      v.hom.app (((Etale.lowerStar B r).rightDerivedFunctorPlus).obj N) ≫
        Q₁.map (a.counit.app N) := by
    apply (cancel_epi ((fixedComparisonPullbackPlus A r).hom.app
      (((Etale.lowerStar B r).rightDerivedFunctorPlus).obj N))).mp
    simpa only [v, a, b, Q₁, χ, B, Etale.rightDerivedLowerStarPlus, Iso.symm_hom,
      Iso.hom_inv_id_app_assoc,
      Category.assoc] using
      fixedComparisonDirectImageMatePlus_counit A r N
  have hk (N) : k'.hom.app (Q₂.obj N) ≫ U₁'.map (v.hom.app N) ≫
      v₁.hom.app (((Etale.upperStar B r).mapDerivedCategoryPlus).obj N) =
        v₂.hom.app N ≫ Q.map (k.hom.app N) := by
    have he := closure_pullback_comp A j₁ r j₂ h N
    apply (cancel_epi ((fixedComparisonPullbackPlus A j₂).hom.app N)).mp
    simp only [v₂, Iso.symm_hom, Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc, ← Category.assoc, he]
    dsimp only [U₁', B]
    simp only [v, v₁, Iso.symm_hom, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Functor.comp_obj,
      Category.comp_id]
    rfl
  have hχ (N) : U₂'.map (χ.app N) ≫
      (restrictionPlus A r j₁ j₂ h).app (Q₁.obj N) ≫ v₁.hom.app N =
      v₂.hom.app (((Etale.lowerStar B r).rightDerivedFunctorPlus).obj N) ≫ Q.map (ρ.app N) := by
    simpa only [ρ, restrictionPlus, b, k', U₁', B, Functor.map_comp,
      Category.assoc] using
      Etale.restriction_coefficient_mate a b U₁ U₂ U₁' U₂' Q Q₁ Q₂
        k k' v₁ v₂ v χ hc hk N
  have hu {T : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j] :
      (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j).unit.app (Q.obj L) ≫
        (upperStar B j).mapDerivedCategoryPlus.map
          ((properOpenSiteExtensionIso A j).inv.app L) =
      Q.map ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j).unit.app L) ≫
        (fixedComparisonPullbackPlus A j).hom.app
          ((Etale.openImmersionLowerShriek B j).mapDerivedCategoryPlus.obj L) := by
    dsimp only [B, Q]
    rw [derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus,
      Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus]
    rw [← closure_plus_unit A j L]
    simp only [Category.assoc, ← Functor.map_comp, closureSquareOpenComparison,
      properOpenSiteExtensionIso, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Functor.comp_obj, Category.comp_id]
  have hm : (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j₂
      ).homEquiv _ _ (Etale.properOpenComparison A r j₁ j₂ h L) ≫
        ρ.app ((Etale.openImmersionLowerShriek B j₁).mapDerivedCategoryPlus.obj L) =
      (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j₁).unit.app L := by
    have ht := Etale.properOpenIdentification_unit A r j₁ j₂ h L
    have ha : (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j₂
        ).homEquiv _ _ (Etale.properOpenComparison A r j₁ j₂ h L) =
        (Etale.properOpenIdentification A r j₁ j₂ h L).inv :=
      (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j₂
        ).homEquiv _ _ |>.apply_symm_apply _
    rw [ha]
    dsimp only [ρ, k, a, U₁, B, Etale.derivedUpperStarLowerStarAdjunctionPlus]
    rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
    dsimp only [Etale.rightDerivedLowerStarPlus] at ht
    rw [← ht]
    exact (Etale.properOpenIdentification A r j₁ j₂ h L).inv_hom_id_assoc _
  have ht := transport_normalization
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j₁)
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j₂)
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j₁)
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j₂)
    ((Etale.lowerStar B r).rightDerivedFunctorPlus)
    ((lowerStar B r).rightDerivedFunctorPlus) Q Q₁ Q₂ ρ
    (restrictionPlus A r j₁ j₂ h) v₁ v₂ χ hχ L
    (Etale.properOpenComparison A r j₁ j₂ h L)
    ((properOpenSiteExtensionIso A j₁).app L)
    ((properOpenSiteExtensionIso A j₂).app L) (hu j₁) (hu j₂) hm
  simpa only [properOpenProEtaleIsoPlus, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, asIso_hom,
    fixedComparisonDirectImageMatePlus, χ, Q, Q₂, B] using ht

private theorem included_restriction
    (A : Type (u + 1)) [CommRing A]
    {X T₁ T₂ : Scheme.{u}} (r : T₁ ⟶ T₂)
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ r = j₂)
    (N : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T₁) (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) j₂).mapDerivedCategory.map
        ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlusCompatibility.hom.app N) ≫
      (properOpenRestriction A r j₁ j₂ h).app N.obj =
        DerivedCategory.Plus.ι.map ((restrictionPlus A r j₁ j₂ h).app N) := by
  let B := ModuleCat.{u + 1} A
  let k := Functor.mapDerivedCategoryNatIso
      (upperStarCongr B h.symm ≪≫ upperStarComp B j₁ r) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  have hn := k.hom.naturality
    ((lowerStar B r).rightDerivedFunctorPlusCompatibility.hom.app N)
  dsimp only [Functor.comp_map] at hn
  have hc := included_counit (upperStarLowerStarAdjunction B r) N
  have hk (Z : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T₂) B)) :
      DerivedCategory.Plus.ι.map
        ((closureSquareProEtalePullComp A j₁ r j₂ h).hom.app Z) = k.hom.app Z.obj := by
    simp only [closureSquareProEtalePullComp, k, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    rfl
  change _ ≫ k.hom.app _ ≫ _ = _
  simp only [restrictionPlus, Functor.map_comp, hk]
  change _ ≫ k.hom.app _ ≫ _ = k.hom.app _ ≫
    (upperStar B j₁).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map
        ((derivedUpperStarLowerStarAdjunctionPlus B r).counit.app N))
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  rw [← hc]
  rw [derivedUpperStarLowerStarAdjunctionPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  rfl

private theorem open_unit_inclusion
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} A) j).unit.app K) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit.app K.obj := by
  dsimp only [derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus,
    derivedOpenImmersionLowerShriekUpperStarAdjunction,
    Adjunction.mapDerivedCategoryPlusAdjunction]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Functor.mapDerivedCategoryPlusCompatibility]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- The transported proper/open map has the open-unit normalization on its original
bounded-below etale input, before coefficient realization or witness conjugation. -/
theorem properOpenProEtaleIso_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T₁ T₂ : Scheme.{u}} (r : T₁ ⟶ T₂) [IsProper r]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ r = j₂)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j₂).homEquiv _ _
        (properOpenProEtaleIso A r j₁ j₂ h L).hom ≫
      (properOpenRestriction A r j₁ j₂ h).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategory.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj)) =
    (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j₁).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj)  := by
  let B := ModuleCat.{u + 1} A
  let K := (comparisonUpperStar B X).mapDerivedCategoryPlus.obj L
  let N := (openImmersionLowerShriek B j₁).mapDerivedCategoryPlus.obj K
  let m := (properOpenProEtaleIsoPlus A r j₁ j₂ h L).hom
  have hp := congrArg (fun z ↦ DerivedCategory.Plus.ι.map z)
    (plus_normalization A r j₁ j₂ h L)
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] at hp
  change DerivedCategory.Plus.ι.map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j₂).unit.app K) ≫
    (upperStar B j₂).mapDerivedCategory.map (DerivedCategory.Plus.ι.map m) ≫
    DerivedCategory.Plus.ι.map ((restrictionPlus A r j₁ j₂ h).app N) =
    DerivedCategory.Plus.ι.map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus B j₁).unit.app K) at hp
  rw [open_unit_inclusion A j₂ K, open_unit_inclusion A j₁ K,
    ← included_restriction A r j₁ j₂ h N] at hp
  dsimp only [properOpenProEtaleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.app, Iso.refl]
  dsimp only [NatTrans.id_app]
  repeat' erw [CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj]
  repeat' erw [Category.id_comp]
  repeat' erw [Category.comp_id]
  erw [Adjunction.homEquiv_unit]
  change ((derivedOpenImmersionLowerShriekUpperStarAdjunction B j₂).unit.app K.obj ≫
    (upperStar B j₂).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map m ≫
        (lowerStar B r).rightDerivedFunctorPlusCompatibility.hom.app N)) ≫
    (properOpenRestriction A r j₁ j₂ h).app N.obj =
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B j₁).unit.app K.obj
  erw [(upperStar B j₂).mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  exact hp

end AlgebraicGeometry.ProEtale
