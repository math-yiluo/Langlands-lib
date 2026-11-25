/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf

import WeilConjectures.AlgebraicGeometry.EtalePullbackSingleComp
public import WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem invert_square
    {C : Type*} [Category C] {W X Y Z V : C}
    (d : W ≅ X) (b : Y ≅ Z) (c : Z ≅ V) (p : X ⟶ Y) (s : W ⟶ V)
    (h : p ≫ b.hom ≫ c.hom = d.inv ≫ s) :
    s ≫ c.inv ≫ b.inv = d.hom ≫ p := by
  rw [← cancel_epi d.inv]
  simp only [Iso.inv_hom_id_assoc, ← reassoc_of% h,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem invert_square_map
    {C D : Type*} [Category C] [Category D] (P : D ⥤ C)
    {W Z V K' : C} {A B K : D}
    (d : W ≅ P.obj A) (b : P.obj B ≅ Z) (c : Z ≅ V)
    (f : A ⟶ B) (s : W ⟶ V)
    (h : P.map f ≫ b.hom ≫ c.hom = d.inv ≫ s)
    (z : B ⟶ K) (t : P.obj K ⟶ K') :
    s ≫ c.inv ≫ b.inv ≫ P.map z ≫ t = d.hom ≫ P.map (f ≫ z) ≫ t := by
  have hc := invert_square d b c (P.map f) s h
  rw [P.map_comp]
  simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ P.map z ≫ t) hc

private theorem adjunct_transition
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ E} {R' : E ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (P : D ⥤ E) (θ : L' ⟶ L ⋙ P)
    {X : C} {K : D} {K' : E} (f : L.obj X ⟶ K) (t : P.obj K ⟶ K') :
    adj'.homEquiv _ _ (θ.app X ≫ P.map f ≫ t) =
      adj.homEquiv _ _ f ≫ adj.transitionThrough adj' P θ K K' t := by
  have ht : adj.transitionThrough adj' P θ K K' t =
      adj'.homEquiv _ _ (θ.app (R.obj K) ≫ P.map (adj.counit.app K) ≫ t) := by
    rw [Adjunction.homEquiv_unit]
    rfl
  rw [ht, ← (adj'.homEquiv _ _).symm.injective.eq_iff,
    Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply]
  rw [reassoc_of% (θ.naturality (adj.homEquiv _ _ f))]
  rw [← Functor.map_comp_assoc]
  have hc := (adj.homEquiv X K).symm_apply_apply f
  change L.map (adj.homEquiv X K f) ≫ adj.counit.app K = f at hc
  rw [hc]

/-- Passing raw triangle pullback through the derived adjunction gives the mate
of the pullback-composition comparison at the shifted coefficient objects.

Proof: invert the pullback/single-functor comparison from upperStarPlusComp_single
and compose it with the raw pullback formula. Naturality of the left-adjoint
comparison moves an adjunct through this composite. Applying the inverse
adjunction equivalence reduces the equality to naturality and the counit identity.
This calculation precedes applying any homology functor, so it is only the
adjunction part of the raw-transition/toHom comparison.
Source: Stacks Project Tags 03Q8 and 09Z1; upperStarPlusComp_single and Mathlib
Adjunction.homEquiv_naturality_left_symm.
(blueprint: sbc-lem-module-raw-triangle-adjunct). -/
theorem higherDirectImageRawTrianglePullback_adjunct
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale)
    (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)).homEquiv _ _
      (((((a ≫ h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((freeSheaf Λ S).obj U)) ≫
        higherDirectImageRawTrianglePullback Λ a h (a ≫ h) rfl q K K' v U z) =
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).homEquiv _ _
      (((((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((freeSheaf Λ S).obj U)) ≫ z) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).derivedPlus.transitionThrough
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (a ≫ h)).derivedPlus
        D+((a)^*[ModuleCat.{u + 1} Λ])
        (upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom (K⟦q⟧) (K'⟦q⟧)
        ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
          (shiftFunctor _ q).map v)  := by
  convert adjunct_transition
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h)
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h))
    D+((a)^*[ModuleCat.{u + 1} Λ])
    (upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom
    (((((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
      ((freeSheaf Λ S).obj U)) ≫ z)
    ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
      (shiftFunctor _ q).map v) using 1
  · congr 1
    change _ ≫ ((DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) a h (a ≫ h) rfl).hom.app
        ((freeSheaf Λ S).obj U)) ≫
      ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app
        (((h)^*[ModuleCat.{u + 1} Λ]).obj ((freeSheaf Λ S).obj U))) ≫
      D+((a)^*[ModuleCat.{u + 1} Λ]).map z ≫ _) = _
    have hc := upperStarPlusComp_single Λ a h ((freeSheaf Λ S).obj U)
    exact invert_square_map D+((a)^*[ModuleCat.{u + 1} Λ])
      ((upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((freeSheaf Λ S).obj U)))
      ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app
        (((h)^*[ModuleCat.{u + 1} Λ]).obj ((freeSheaf Λ S).obj U)))
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
        ((upperStarComp (ModuleCat.{u + 1} Λ) a h (a ≫ h) rfl).app
          ((freeSheaf Λ S).obj U)).symm)
      _ _ hc z _
  · simp only [derivedUpperStarLowerStarAdjunctionPlus,
      Adjunction.derivedAdjunctionPlus_eq_derivedPlus]

end AlgebraicGeometry.Etale
