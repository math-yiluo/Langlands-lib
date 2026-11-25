/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Compatibility laws for the right-derived unit on complexes

The laws are proved directly from the quotient comparison isomorphisms.
Source: Stacks Tags 070I and 015F
(blueprint: lem-cbc-derived-complex-unit-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w₁ w₂ v₁ v₂ u₁ u₂
namespace CategoryTheory
open Abelian Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  [HasKInjectiveResolutions C]

/-- The right-derived unit transferred from homotopy complexes to complexes by the
canonical quotient comparison. This is an explicit composite, with no chosen data.
Source: Stacks Tag 015F (blueprint: lem-cbc-derived-complex-unit-compatibility). -/
@[no_expose] def derivedComplexUnit (F : C ⥤ D) [F.Additive] (J : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj J) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj J) :=
  (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj J) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app J)

/-- The transferred unit is inverse to its K-injective value isomorphism, is natural,
respects exact factorization, and restricts to the bounded-below derived unit.
Proof: unfold the explicit quotient-unit-quotient composite and use the
naturality of the quotient comparisons and of the derived units.
Source: Stacks Tags 070I and 015F
(blueprint: lem-cbc-derived-complex-unit-compatibility). -/
theorem derivedComplexUnitCompatibility :
    (∀ (F : C ⥤ D) [F.Additive] (J : CochainComplex C ℤ) [J.IsKInjective],
      derivedComplexUnit F J ≫ (F.rightDerivedFunctorObjQIso J).hom = 𝟙 _) ∧
    (∀ (F : C ⥤ D) [F.Additive] {J I : CochainComplex C ℤ} (ρ : J ⟶ I),
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map ρ) ≫
        derivedComplexUnit F I =
        derivedComplexUnit F J ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map ρ)) ∧
    (∀ (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      (J : CochainComplex C ℤ),
      F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient C (.up ℤ)).obj J) ≫
          F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app J) ≫
          F.mapDerivedCategoryFactors.hom.app J =
        (DerivedCategory.quotientCompQhIso D).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj J)) ∧
    (∀ [EnoughInjectives C] (F : C ⥤ D) [F.Additive] (K : HomotopyCategory.Plus C),
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app K) ≫
          F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.Plus.ι C).obj K)) := by
  refine ⟨fun F _ J _ ↦ ?_, fun F _ J I ρ ↦ ?_, fun F _ _ _ J ↦ ?_, fun F _ K ↦ ?_⟩
  · simp [derivedComplexUnit, Functor.rightDerivedFunctorObjQIso, Category.assoc]
  · have h := F.rightDerivedFunctorUnit.naturality
      ((HomotopyCategory.quotient C (.up ℤ)).map ρ)
    simp only [Functor.comp_map] at h
    simp only [derivedComplexUnit, Category.assoc]
    rw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
    have hf : ((F.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient C (.up ℤ)).map ρ)) =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((F.mapHomologicalComplex (.up ℤ)).map ρ) := rfl
    rw [← hf, reassoc_of% h, ← Functor.map_comp]
    rw [DerivedCategory.quotientCompQhIso_hom_naturality]
    rw [Functor.map_comp]
  · have he : F.mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj J) =
      F.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso C).app J) ≪≫
        F.mapDerivedCategoryFactors.app J ≪≫
          ((DerivedCategory.quotientCompQhIso D).app
            ((F.mapHomologicalComplex (.up ℤ)).obj J)).symm := by
      apply Iso.ext
      simp only [Iso.app_hom, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
        Functor.mapDerivedCategoryFactorsh_hom_app, Functor.mapHomotopyCategoryFactors,
        Quotient.lift.isLift_inv]
      erw [DerivedCategory.Qh.map_id, Category.comp_id]
      rfl
    have hi := congrArg Iso.inv he
    change F.mapDerivedCategoryFactorsh.inv.app _ = _ at hi
    rw [hi]
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv,
      Iso.app_hom, Category.assoc]
    rw [← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app, F.mapDerivedCategory.map_id,
      Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  · simpa only [Functor.rightDerivedFunctorPlusCompatibility, Functor.rightDerivedUnique,
      Functor.rightDerivedNatIso_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
      Functor.rightDerivedFunctorPlusιUnit, Functor.ιRightDerivedFunctorUnit,
      Functor.whiskerRight_app, Functor.whiskerLeft_app] using
        (Functor.rightDerivedNatTrans_app
          (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
          (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
          F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
          (HomotopyCategory.Plus.quasiIso C) (𝟙 _) K)

end CategoryTheory
