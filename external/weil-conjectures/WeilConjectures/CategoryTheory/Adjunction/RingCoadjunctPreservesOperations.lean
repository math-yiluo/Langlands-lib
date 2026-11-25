/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! Operation preservation for the inverse restricted adjunct. -/

@[expose] public section

universe vA vB uA uB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Adjunction

set_option autoImplicit false

private theorem coadjunct_tensor
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    [PreservesFiniteProducts L] [PreservesFiniteProducts R]
    {X : A} {Y : B} (k : X ⟶ R.obj Y) :
    (prodComparisonIso L X X).inv ≫
        (adj.homEquiv (X ⊗ X) (Y ⊗ Y)).symm
          ((k ⊗ₘ k) ≫ (prodComparisonIso R Y Y).inv) =
      ((adj.homEquiv X Y).symm k ⊗ₘ (adj.homEquiv X Y).symm k) := by
  have hf (F : A ⥤ B) [PreservesFiniteProducts F] (Z : A) :
      (prodComparisonIso F Z Z).inv ≫ F.map (fst Z Z) = fst _ _ := by
    rw [← CartesianMonoidalCategory.prodComparison_fst, ← prodComparisonIso_hom]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hs (F : A ⥤ B) [PreservesFiniteProducts F] (Z : A) :
      (prodComparisonIso F Z Z).inv ≫ F.map (snd Z Z) = snd _ _ := by
    rw [← CartesianMonoidalCategory.prodComparison_snd, ← prodComparisonIso_hom]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hfR : (prodComparisonIso R Y Y).inv ≫ R.map (fst Y Y) = fst _ _ := by
    rw [← CartesianMonoidalCategory.prodComparison_fst, ← prodComparisonIso_hom]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hsR : (prodComparisonIso R Y Y).inv ≫ R.map (snd Y Y) = snd _ _ := by
    rw [← CartesianMonoidalCategory.prodComparison_snd, ← prodComparisonIso_hom]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, ← adj.homEquiv_naturality_right_symm]
    simp only [Category.assoc, hfR, tensorHom_fst]
    rw [adj.homEquiv_naturality_left_symm]
    simp only [← Category.assoc, hf]
  · rw [Category.assoc, ← adj.homEquiv_naturality_right_symm]
    simp only [Category.assoc, hsR, tensorHom_snd]
    rw [adj.homEquiv_naturality_left_symm]
    simp only [← Category.assoc, hs]

private theorem coadjunct_binary
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    [PreservesFiniteProducts L] [PreservesFiniteProducts R]
    {X : A} {Y : B} (k : X ⟶ R.obj Y)
    (mX : X ⊗ X ⟶ X) (mY : Y ⊗ Y ⟶ Y)
    (h : mX ≫ k = (k ⊗ₘ k) ≫ (prodComparisonIso R Y Y).inv ≫ R.map mY) :
    (prodComparisonIso L X X).inv ≫ L.map mX ≫ (adj.homEquiv X Y).symm k =
      ((adj.homEquiv X Y).symm k ⊗ₘ (adj.homEquiv X Y).symm k) ≫ mY := by
  rw [← adj.homEquiv_naturality_left_symm, h,
    ← Category.assoc (k ⊗ₘ k), adj.homEquiv_naturality_right_symm,
    ← Category.assoc, coadjunct_tensor]

private theorem coadjunct_constant
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    [PreservesFiniteProducts L] [PreservesFiniteProducts R]
    {X : A} {Y : B} (k : X ⟶ R.obj Y)
    (qX : 𝟙_ A ⟶ X) (qY : 𝟙_ B ⟶ Y)
    (h : qX ≫ k = (preservesTerminalIso R).inv ≫ R.map qY) :
    (preservesTerminalIso L).inv ≫ L.map qX ≫ (adj.homEquiv X Y).symm k = qY := by
  rw [← adj.homEquiv_naturality_left_symm, h,
    adj.homEquiv_naturality_right_symm, ← Category.assoc]
  have ht : (preservesTerminalIso L).inv ≫
      (adj.homEquiv (𝟙_ A) (𝟙_ B)).symm (preservesTerminalIso R).inv = 𝟙 _ :=
    toUnit_unique _ _
  rw [ht, Category.id_comp]

/-- The inverse adjunct preserves ring operations.
Source: Stacks Project, Proposition 00YV, proof of (2), extended there to rings.

Proof: For a binary operation m, let rho be R's product comparison and lambda L's. Naturality of
epsilon at the two projections, together with the projection equations of rho and lambda, gives
L(rho inverse) followed by epsilon_(Y times Y) equal to lambda_(RY,RY) followed by (epsilon_Y
times epsilon_Y). Check this equality by composing with each projection; cancel the invertible
product comparisons when checking. Naturality of epsilon at m_Y then identifies the composite of L
of the transported binary operation with epsilon_Y with the product of epsilon_Y's followed by
m_Y. Substitute opsL and opsR and the equation m_X followed by g equals (g times g) followed by
m_(RF Y). Cancel eL and eR to obtain m_(LF X) followed by the conjugated inverse adjunct equal to
the product of two copies of that adjunct followed by m_Y. Apply this to addition and
multiplication. For a constant q, naturality at q_Y and uniqueness of the map into the terminal
object identify the composite of the inverse terminal comparisons and epsilon_terminal with the
identity. With the constant equations opsL, opsR, and that for g, this proves q_(LF X) followed by
the inverse adjunct equals q_Y, both for zero and for one. Package zero and addition as
IsAddMonHom and one and multiplication as IsMonHom; these give IsRingHom. Negation preservation
follows from additivity and is not a field of IsRingHom.
(blueprint: lem-weil-pbc-ring-coadjunct-preserves-operations)
-/
theorem ringCoadjunctPreservesOperations
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    [PreservesFiniteProducts L] [PreservesFiniteProducts R]
    [BraidedCategory A] [BraidedCategory B]
    (LF : CommRingObjCat A ⥤ CommRingObjCat B) (RF : CommRingObjCat B ⥤ CommRingObjCat A)
    (hL : LF ⋙ CommRingObjCat.forget B = CommRingObjCat.forget A ⋙ L)
    (hR : RF ⋙ CommRingObjCat.forget A = CommRingObjCat.forget B ⋙ R)
    (opsL : let eL := eqToIso hL; (∀ X : CommRingObjCat A,
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
              (preservesTerminalIso L).inv ≫ L.map (MonObj.one (X := X.X))))
    (opsR : let eR := eqToIso hR; (∀ X : CommRingObjCat B,
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
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X)))) :
    ∀ (X : CommRingObjCat A) (Y : CommRingObjCat B) (g : X ⟶ RF.obj Y),
      IsRingHom (show (LF.obj X).X ⟶ Y.X from (eqToIso hL).hom.app X ≫
        (adj.homEquiv X.X Y.X).symm (g.hom ≫ (eqToIso hR).hom.app Y)) := by
  intro X Y g
  let eL := (eqToIso hL).hom.app X
  let eR := (eqToIso hR).hom.app Y
  let k := g.hom ≫ eR
  let f := (adj.homEquiv X.X Y.X).symm k
  have binary (mX : X.X ⊗ X.X ⟶ X.X)
      (mLX : (LF.obj X).X ⊗ (LF.obj X).X ⟶ (LF.obj X).X)
      (mY : Y.X ⊗ Y.X ⟶ Y.X)
      (mRY : (RF.obj Y).X ⊗ (RF.obj Y).X ⟶ (RF.obj Y).X)
      (hl : mLX ≫ eL = (eL ⊗ₘ eL) ≫
        (prodComparisonIso L X.X X.X).inv ≫ L.map mX)
      (hr : mRY ≫ eR = (eR ⊗ₘ eR) ≫
        (prodComparisonIso R Y.X Y.X).inv ≫ R.map mY)
      (hg : mX ≫ g.hom = (g.hom ⊗ₘ g.hom) ≫ mRY) :
      mLX ≫ (eL ≫ f) = ((eL ≫ f) ⊗ₘ (eL ≫ f)) ≫ mY := by
    have hk : mX ≫ k = (k ⊗ₘ k) ≫
        (prodComparisonIso R Y.X Y.X).inv ≫ R.map mY := by
      dsimp [k]
      rw [← Category.assoc, hg, Category.assoc, hr]
      simp only [← tensorHom_comp_tensorHom, Category.assoc]
    have hb := coadjunct_binary adj (X := X.X) (Y := Y.X) k mX mY hk
    change mLX ≫ (eL ≫ f) = _
    rw [← Category.assoc, hl]
    simpa only [f, Category.assoc, ← tensorHom_comp_tensorHom] using
      congrArg ((eL ⊗ₘ eL) ≫ ·) hb
  have constant (qX : 𝟙_ A ⟶ X.X) (qLX : 𝟙_ B ⟶ (LF.obj X).X)
      (qY : 𝟙_ B ⟶ Y.X) (qRY : 𝟙_ A ⟶ (RF.obj Y).X)
      (hl : qLX ≫ eL = (preservesTerminalIso L).inv ≫ L.map qX)
      (hr : qRY ≫ eR = (preservesTerminalIso R).inv ≫ R.map qY)
      (hg : qX ≫ g.hom = qRY) : qLX ≫ (eL ≫ f) = qY := by
    have hk : qX ≫ k = (preservesTerminalIso R).inv ≫ R.map qY := by
      dsimp [k]
      rw [← Category.assoc, hg, hr]
    rw [← Category.assoc, hl]
    simpa only [f, Category.assoc] using coadjunct_constant adj (X := X.X) (Y := Y.X) k qX qY hk
  exact
    { zero_hom := constant _ _ _ _ (opsL X).2.1 (opsR Y).2.1
        (IsAddMonHom.zero_hom g.hom)
      add_hom := binary _ _ _ _ (opsL X).1 (opsR Y).1
        (IsAddMonHom.add_hom g.hom)
      one_hom := constant _ _ _ _ (opsL X).2.2.2.2 (opsR Y).2.2.2.2
        (IsMonHom.one_hom g.hom)
      mul_hom := binary _ _ _ _ (opsL X).2.2.2.1 (opsR Y).2.2.2.1
        (IsMonHom.mul_hom g.hom) }

end CategoryTheory.Adjunction
