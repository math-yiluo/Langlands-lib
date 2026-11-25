/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Canonical single comparison under exact postcomposition

Source: Stacks Project, Tag 0AVW, canonical affine factorization.
(blueprint: lem-sc-single-right-derived-exact-composition).
-/

@[expose] public section

universe uC uA uB vC vA vB wC wA wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

variable {C : Type uC} {A : Type uA} {B : Type uB}
  [Category.{vC} C] [Category.{vA} A] [Category.{vB} B]
  [Abelian C] [Abelian A] [Abelian B]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wA} A]
  [HasDerivedCategory.{wB} B] [HasKInjectiveResolutions C]

/-- The canonical single-to-right-derived comparison commutes with exact postcomposition.
Source: Stacks Project, Tag 0AVW, canonical factorization of affine pushforward
(blueprint: lem-sc-single-right-derived-exact-composition).

Proof: Expand the comparison for the composite right-derived functor. Uniqueness of
right derived functors identifies its composite with the composite of the two units.
Postcomposing the second unit with its exact-functor comparison gives the inverse
localization comparison. Naturality of that comparison moves the inverse single map
through it. The termwise single comparisons compose, leaving the canonical single
comparison for F followed by T. This is an equality of canonical maps, valid also for
zero objects and zero functors. -/
theorem single_rightDerived_exact_composition (F : C ⥤ A) (T : A ⥤ B)
    [F.Additive] [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (M : C) :
    (T.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M) ≫
      T.mapDerivedCategory.map
        (DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M) ≫
          cast (by rfl) (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
            ((CochainComplex.singleFunctor C 0).obj M)))) ≫
      (rightDerivedFunctorCompMapDerivedCategoryIso F T).inv.app
        ((DerivedCategory.singleFunctor C 0).obj M) =
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (F ⋙ T)
        (ComplexShape.up ℤ) 0).inv.app M) ≫
      cast (by rfl) ((F ⋙ T).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((CochainComplex.singleFunctor C 0).obj M))) := by
  apply (cancel_mono ((rightDerivedFunctorCompMapDerivedCategoryIso F T).hom.app
    ((DerivedCategory.singleFunctor C 0).obj M))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  simp only [rightDerivedFunctorCompMapDerivedCategoryIso]
  rw [rightDerivedNatIso_hom]
  erw [rightDerivedNatTrans_app]
  dsimp [rightDerivedFunctorCompMapDerivedCategoryUnit]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp]
  simp only [← Category.assoc]
  apply congrArg (fun f ↦ f ≫ T.mapDerivedCategory.map
    (F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M)))
  dsimp [mapHomotopyCategoryCompIso, Quotient.natIsoLift, Quotient.natTransLift,
    mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex]
  simp only [NatTrans.mapHomologicalComplex_id, NatTrans.id_app, Functor.map_id]
  have ht (K : CochainComplex A ℤ) :
      T.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
        T.mapDerivedCategoryFactors.hom.app K := by
    rw [T.mapDerivedCategoryFactorsh_hom_app]
    change T.mapDerivedCategory.map (𝟙 _) ≫ T.mapDerivedCategoryFactors.hom.app K ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    simp only [Functor.map_id, Category.id_comp]
    exact Category.comp_id _
  have ht' (K : CochainComplex A ℤ) :
      T.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K) =
        T.mapDerivedCategoryFactors.inv.app K := by
    apply (cancel_epi
      (T.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K))).mp
    rw [Iso.hom_inv_id_app, ht, Iso.hom_inv_id_app]
    rfl
  erw [ht']
  erw [Category.comp_id]
  apply (cancel_mono (T.mapDerivedCategoryFactors.hom.app
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj M)))).mp
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  erw [T.mapDerivedCategoryFactors_hom_naturality]
  rw [← Category.assoc]
  erw [T.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  rw [← DerivedCategory.Q.map_comp]
  apply congrArg DerivedCategory.Q.map
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    simp [mapCochainComplexSingleFunctor]
  · simp [mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_ne, hi]

end CategoryTheory.Functor
