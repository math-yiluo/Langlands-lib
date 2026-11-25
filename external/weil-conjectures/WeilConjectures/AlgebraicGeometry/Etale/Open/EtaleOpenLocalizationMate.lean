/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
public import Mathlib.Algebra.Homology.Localization

import all Mathlib.Algebra.Homology.Localization

/-! # The adjunction mate of exact open localization. -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
open scoped CategoryTheory.Functor CategoryTheory.TwoSquare
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

open CategoryTheory.Limits

private theorem mate_of_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {M : E ⥤ F} {S : F ⥤ E}
    (a : L ⊣ R) (b : M ⊣ S) {G : C ⥤ E} {H : D ⥤ F}
    (α : TwoSquare G L M H) (δ : TwoSquare R H G S)
    (h : ∀ X, G.map (a.unit.app X) ≫ δ.app (L.obj X) =
      b.unit.app (G.obj X) ≫ S.map (α.app X)) :
    mateEquiv a b α = δ := by
  apply (mateEquiv a b).symm.injective
  rw [Equiv.symm_apply_apply]
  ext X
  apply (b.homEquiv _ _).injective
  change b.unit.app _ ≫ S.map _ = b.unit.app _ ≫ S.map _
  exact (h X).symm.trans (unit_mateEquiv_symm a b δ X)

private theorem exactFactorh
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj P)) ≫
    F.mapDerivedCategoryFactors.hom.app P ≫
      𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map
          (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj P))) = _
  have hi : DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P))) =
      𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
    DerivedCategory.Qh.map_id _
  rw [hi, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Category.comp_id]
  exact Category.comp_id _

private theorem open_unit
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
        (DerivedCategory.Q.obj P) ≫
      (derivedRestriction (A := A) j).map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app P) ≫
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app
        (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
          (.up ℤ)).obj P) =
    DerivedCategory.Q.map
      (((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).unit.app P) := by
  have h := (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction_unit_app_fac
      ((HomotopyCategory.quotient _ _).obj P)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  change _ ≫ _ ≫ _ = DerivedCategory.Q.map
    (((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).unit.app P) at h
  change _ ≫ (derivedRestriction (A := A) j).map
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj P)) ≫
    (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj
        (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
          (.up ℤ)).obj P)) = _ at h
  rw [exactFactorh, exactFactorh] at h
  exact h

/-- The right mate of the exact open localization factor is the inverse restriction factor.
Source: Stacks 06YY, 0E8I; normalization proof step 1.

Proof: The derived adjunction unit formula on a homotopy representative identifies its unit
with the localized cochain unit, after postcomposing the two exact localization factors.
The homotopy factors on quotient objects equal the cochain factors. Cancel the restriction
factor, which is an isomorphism. The resulting unit identity characterizes the mate. The
argument holds for every complex and for the empty open immersion.
(blueprint: lem-coef-etale-open-localization-mate). -/
theorem etaleOpenLocalizationMate
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    mateEquiv
      ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ))
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk _ _ _ _
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom) =
      TwoSquare.mk _ _ _ _
        (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.inv := by
  apply mate_of_unit
  intro P
  apply (cancel_mono ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app
      (((openImmersionLowerShriek
        (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact (open_unit A j P).symm

end AlgebraicGeometry.Etale
