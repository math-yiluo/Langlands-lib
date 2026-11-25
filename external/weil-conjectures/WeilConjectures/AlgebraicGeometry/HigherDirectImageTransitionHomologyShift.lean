/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions



import all WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift
import all WeilConjectures.AlgebraicGeometry.DerivedAdjunctionCommShift
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStarPlusComp upperStarComp
  Functor.mapDerivedCategoryPlusSingleFunctor lowerStarPlusTransition
  Adjunction.homEquiv Adjunction.derivedPlus derivedUpperStarLowerStarAdjunctionPlus

private theorem module_transition_shift
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') :
    (lowerStarPlusTransition Λ a h (a ≫ h) rfl (K⟦q⟧) ≫
      R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map
        ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
          (shiftFunctor _ q).map v)) ≫
      (R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K' =
    (R+((h)_*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
      (shiftFunctor _ q).map
        (lowerStarPlusTransition Λ a h (a ≫ h) rfl K ≫
          R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map v) := by
  have : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).derivedPlus.CommShift ℤ :=
    Adjunction.CommShift.mk' _ ℤ
      (derivedUnit_commShift (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h))
  have : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (a ≫ h)).derivedPlus.CommShift ℤ :=
    Adjunction.CommShift.mk' _ ℤ
      (derivedUnit_commShift (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (a ≫ h)))
  have : NatTrans.CommShift (upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom ℤ := by
    unfold upperStarPlusComp
    simp only [Iso.trans_hom]
    have := Functor.plusNatIso_commShift (upperStarComp (ModuleCat.{u + 1} Λ) a h)
    have := comp_preservesFiniteLimits (h)^*[ModuleCat.{u + 1} Λ]
      (a)^*[ModuleCat.{u + 1} Λ]
    have := comp_preservesFiniteColimits (h)^*[ModuleCat.{u + 1} Λ]
      (a)^*[ModuleCat.{u + 1} Λ]
    have := Functor.plusCompIso_commShift (h)^*[ModuleCat.{u + 1} Λ]
      (a)^*[ModuleCat.{u + 1} Λ]
    infer_instance
  simpa only [Adjunction.transitionThrough, lowerStarPlusTransition,
    derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus, eqToIso_refl, Iso.refl_trans,
    Functor.map_comp, Category.assoc] using
    Adjunction.transitionThrough_shift
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).derivedPlus
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (a ≫ h)).derivedPlus
      D+((a)^*[ModuleCat.{u + 1} Λ])
      (upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom K K' v q

private theorem homology_shift_naturality
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (q : ℤ) {X Y : DerivedCategory.Plus C} (t : X ⟶ Y) :
    (DerivedCategory.Plus.homologyFunctor C 0).map ((shiftFunctor _ q).map t) ≫
      ((DerivedCategory.Plus.homologyFunctor C 0).isoShiftZero ℤ).inv.app (Y⟦q⟧) ≫
      ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso q 0 q (add_zero q)).hom.app Y =
    (((DerivedCategory.Plus.homologyFunctor C 0).isoShiftZero ℤ).inv.app (X⟦q⟧) ≫
      ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso q 0 q (add_zero q)).hom.app X) ≫
      (DerivedCategory.Plus.homologyFunctor C q).map t := by
  have n₁ := ((DerivedCategory.Plus.homologyFunctor C 0).isoShiftZero ℤ).inv.naturality
    ((shiftFunctor _ q).map t)
  have n₂ :=
    ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso q 0 q (add_zero q)).hom.naturality t
  erw [reassoc_of% n₁, n₂]
  exact (Category.assoc _ _ _).symm

/-- The canonical transition for derived module sheaves commutes with the comparison
from degree-zero homology of a shifted object to degree-q homology.

Proof: the derived adjunction unit commutes with shifts by computing it on the
homotopy-category localization; the counit then does by the adjunction identities.
The comparison between iterated pullbacks commutes with shifts because the exact
functor comparisons do. Thus the mate defining the transition commutes with shifts.
Apply degree-zero homology, then naturality of its shift-zero and degree-q isomorphisms.
Source: the generic calculations in AbelianDerivedDirectImageTransitionShift and
DerivedAdjunctionCommShift, specialized to ModuleCat rather than AddCommGrpCat.
(blueprint: sbc-lem-module-transition-homology-shift). -/
theorem higherDirectImageTransition_homologyShift
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') :
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).map
      (lowerStarPlusTransition Λ a h (a ≫ h) rfl (K⟦q⟧) ≫
        R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map
          ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
            (shiftFunctor _ q).map v)) ≫
      (DerivedCategory.Plus.homologyFunctor _ 0).map
        ((R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K') ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app
        ((R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).obj K')⟦q⟧) ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app
        (R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).obj K') =
    ((DerivedCategory.Plus.homologyFunctor _ 0).map
        ((R+((h)_*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K) ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app
        ((R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)⟦q⟧) ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app
        (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)) ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (lowerStarPlusTransition Λ a h (a ≫ h) rfl K ≫
          R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map v) := by
  rw [← Functor.map_comp_assoc, module_transition_shift, Functor.map_comp_assoc]
  erw [homology_shift_naturality]
  repeat erw [Category.assoc]
  all_goals rfl


end AlgebraicGeometry.Etale
