/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.TruncationCouple
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! Canonical truncation-couple proof step. -/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The lower-half-plane vanishing of the raw truncation terms.
Source: Stacks Tags 05TC (1), 0118; blueprint step 3 of lemma-uniform-bound-proper-direct-image--1
(blueprint: lem-sp-truncation-quadrant-vanishing).

Proof: For q<a the truncation has zero homology in every degree: below and at q
use the homology isomorphism of its inclusion and the hypothesis on K; above q
use strict upper support. Its image in the derived category is zero, and additive
RF and homology preserve zero objects. For E with q<a the single complex is zero
because H^q(K) is zero. For p<0, RF of the degree-zero single object has no negative
homology; shift it by -q and use commutation of RF and homology with shifts.
Finally transport all three zero-object assertions through `bridgeIso`. -/
theorem truncation_quadrant_vanishing
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (a : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q)) :
    (∀ p q : ℤ, p < 0 → IsZero (TruncationCouple.E F K p q)) ∧
    (∀ p q : ℤ, q < a → IsZero (TruncationCouple.D F K p q)) ∧
    (∀ p q : ℤ, q < a → IsZero (TruncationCouple.E F K p q)) := by
  have hzero : ∀ q : ℤ, q < a →
      IsZero (DerivedCategory.Q.obj (TruncationCouple.truncation K q).obj) := by
    intro q hq
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro i
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctorFactors A i).app _)
    change IsZero ((K.obj.truncLE q).homology i)
    by_cases hi : i ≤ q
    · have := K.obj.quasiIsoAt_ιTruncLE q i hi
      exact (ha i (by omega)).of_iso
        (asIso (HomologicalComplex.homologyMap (K.obj.ιTruncLE q) i))
    · exact ((K.obj.truncLE q).exactAt_of_isLE q i (by omega)).isZero_homology
  refine ⟨?_, ?_, ?_⟩
  · intro p q hp
    let V := K.obj.homology q
    let e := (DerivedCategory.homologyFunctor B (p + q)).mapIso
        (F.rightDerivedFunctor.mapIso
          (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0
            (by omega)).app V).symm) ≪≫
      (DerivedCategory.homologyFunctor B (p + q)).mapIso
        ((F.rightDerivedFunctor.commShiftIso (-q)).app
          ((DerivedCategory.singleFunctor A 0).obj V)) ≪≫
      ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) (p + q) p
        (by omega)).app
          (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj V))
    have := F.isGE_rightDerivedFunctor_obj_singleFunctor V
    have hz := DerivedCategory.isZero_of_isGE
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj V)) 0 p hp
    exact (hz.of_iso e).of_iso
      (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K q) (p + q)).symm
  · intro p q hq
    exact ((DerivedCategory.homologyFunctor B (p + q)).map_isZero
      (F.isZero_rightDerivedFunctor_obj (hzero q hq))).of_iso
        (TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) (p + q)).symm
  · intro p q hq
    have hz := (CochainComplex.singleFunctor A q).map_isZero (ha q hq)
    exact ((DerivedCategory.homologyFunctor B (p + q)).map_isZero
      (F.isZero_rightDerivedFunctor_obj (DerivedCategory.Q.map_isZero hz))).of_iso
        (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K q) (p + q)).symm

end CategoryTheory
