/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.Adjunction.RingHomEquivCore

@[expose] public section

universe vA vB uA uB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Adjunction

/-- Assembly of the lifted ring adjunction from single-functor transport and the
restricted natural hom-bijection.
(blueprint: lem-weil-pbc-lifted-comm-ring-branch)
Source: Stacks Project, Proposition 00YV, paragraph on rings as sextuples.

Proof: apply finiteProductRingFunctor separately to L and R. Their operation
formulas permit ringHomEquivCore to restrict the original natural hom-bijection.
Apply Mathlib's mkOfHomEquiv to that core; its hom-equivalence is the supplied one.
The unit and counit are its values on identities and inverse values on identities,
respectively. The final existence criterion follows by applying this equivalence
in one direction and its inverse in the other, using injectivity of the original
adjunction hom-equivalence for the backward equation. -/
theorem liftedCommRingBranch
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [PreservesFiniteProducts L]
    [PreservesFiniteProducts R] :
    letI : BraidedCategory A := BraidedCategory.ofCartesianMonoidalCategory
    letI : BraidedCategory B := BraidedCategory.ofCartesianMonoidalCategory
    (∃ (LF : CommRingObjCat A ⥤ CommRingObjCat B) (RF : CommRingObjCat B ⥤ CommRingObjCat A)
          (hL : LF ⋙ CommRingObjCat.forget B = CommRingObjCat.forget A ⋙ L)
          (hR : RF ⋙ CommRingObjCat.forget A = CommRingObjCat.forget B ⋙ R),
        let eL := eqToIso hL
        let eR := eqToIso hR
        ∃ (a : LF ⊣ RF),
          (∀ X : CommRingObjCat A,
            AddMonObj.add (X := (LF.obj X).X) ≫ eL.hom.app X =
              (eL.hom.app X ⊗ₘ eL.hom.app X) ≫
                (prodComparisonIso L X.X X.X).inv ≫ L.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (LF.obj X).X) ≫ eL.hom.app X =
              (preservesTerminalIso L).inv ≫ L.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (LF.obj X).X) ≫ eL.hom.app X =
              eL.hom.app X ≫ L.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (LF.obj X).X) ≫ eL.hom.app X =
              (eL.hom.app X ⊗ₘ eL.hom.app X) ≫
                (prodComparisonIso L X.X X.X).inv ≫ L.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (LF.obj X).X) ≫ eL.hom.app X =
              (preservesTerminalIso L).inv ≫ L.map (MonObj.one (X := X.X))) ∧
          (∀ X : CommRingObjCat B,
            AddMonObj.add (X := (RF.obj X).X) ≫ eR.hom.app X =
              (eR.hom.app X ⊗ₘ eR.hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (RF.obj X).X) ≫ eR.hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (RF.obj X).X) ≫ eR.hom.app X =
              eR.hom.app X ≫ R.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (RF.obj X).X) ≫ eR.hom.app X =
              (eR.hom.app X ⊗ₘ eR.hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (RF.obj X).X) ≫ eR.hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X))) ∧
          (∀ (X : CommRingObjCat A) (Y : CommRingObjCat B) (f : LF.obj X ⟶ Y),
            (CommRingObjCat.forget A).map (a.homEquiv X Y f) ≫ eR.hom.app Y =
              adj.homEquiv X.X Y.X (eL.inv.app X ≫ (CommRingObjCat.forget B).map f)) ∧
          (∀ X : CommRingObjCat A,
            (CommRingObjCat.forget A).map (a.unit.app X) ≫ eR.hom.app (LF.obj X) ≫
                R.map (eL.hom.app X) = adj.unit.app X.X) ∧
          (∀ Y : CommRingObjCat B,
            L.map (eR.inv.app Y) ≫ eL.inv.app (RF.obj Y) ≫
                (CommRingObjCat.forget B).map (a.counit.app Y) = adj.counit.app Y.X) ∧
          (∀ (X : CommRingObjCat A) (Y : CommRingObjCat B) (α : L.obj X.X ⟶ Y.X),
            (∃ f : LF.obj X ⟶ Y, eL.inv.app X ≫ (CommRingObjCat.forget B).map f = α) ↔
              ∃ g : X ⟶ RF.obj Y,
                (CommRingObjCat.forget A).map g ≫ eR.hom.app Y = adj.homEquiv X.X Y.X α)) := by
  let : BraidedCategory A := BraidedCategory.ofCartesianMonoidalCategory
  let : BraidedCategory B := BraidedCategory.ofCartesianMonoidalCategory
  obtain ⟨LF, hL, opsL⟩ := finiteProductRingFunctor L
  obtain ⟨RF, hR, opsR⟩ := finiteProductRingFunctor R
  obtain ⟨c, hc, hu, hv⟩ := ringHomEquivCore adj LF RF hL hR opsL opsR
  let a : LF ⊣ RF := Adjunction.mkOfHomEquiv c
  have ha (X : CommRingObjCat A) (Y : CommRingObjCat B) (f : LF.obj X ⟶ Y) :
      (CommRingObjCat.forget A).map (a.homEquiv X Y f) ≫ (eqToIso hR).hom.app Y =
        adj.homEquiv X.X Y.X ((eqToIso hL).inv.app X ≫
          (CommRingObjCat.forget B).map f) := by
    simpa only [a, Adjunction.mkOfHomEquiv_homEquiv] using hc X Y f
  refine ⟨LF, RF, hL, hR, a, opsL, opsR, ha, ?_, ?_, ?_⟩
  · intro X
    rw [← a.homEquiv_id X]
    simpa only [a, Adjunction.mkOfHomEquiv_homEquiv] using hu X
  · intro Y
    rw [← a.homEquiv_symm_id Y]
    simpa only [a, Adjunction.mkOfHomEquiv_homEquiv] using hv Y
  · intro X Y α
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨a.homEquiv X Y f, (ha X Y f).trans (congrArg _ hf)⟩
    · rintro ⟨g, hg⟩
      refine ⟨(a.homEquiv X Y).symm g, ?_⟩
      apply (adj.homEquiv X.X Y.X).injective
      rw [← ha, Equiv.apply_symm_apply, hg]

end CategoryTheory.Adjunction
