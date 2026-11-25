/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! Operation preservation for the forward restricted adjunct. -/

@[expose] public section

universe vA vB uA uB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Adjunction

set_option autoImplicit false

/-- The forward adjunct preserves ring operations.
Source: Stacks Project, Proposition 00YV, proof of (2), extended there to rings.

Proof: For a binary operation m, write lambda for the comparison of L and rho for that of R.
Naturality of eta at the two projections gives eta_(X times X) followed by R(lambda) and rho equal
to eta_X times eta_X: the two projections of these maps are eta_X followed by the corresponding
projection. Thus eta_(X times X) followed by R(lambda) equals (eta_X times eta_X) followed
by rho inverse. Naturality at m_X gives m_X followed by eta_X equal to eta_(X times X) followed by
RL(m_X). Combine these identities with opsL, opsR, and the equation m_(LF X) followed by f equals
(f times f) followed by m_Y. Cancel the component isomorphisms eL and eR to obtain m_X followed by
the displayed conjugated adjunct equal to the product of two copies of that adjunct followed by
m_(RF Y). Apply this once to addition and once to multiplication. For a constant q, naturality at
q_X gives q_X followed by eta_X equal to eta_terminal followed by RL(q_X). The composite of
eta_terminal with the images of the two terminal comparison maps is the unique terminal
endomorphism, hence the identity. Using opsL, opsR and the constant equation for f gives q_X
followed by the conjugated adjunct equal to q_(RF Y), for q zero and one. The zero and addition
equations give IsAddMonHom; the one and multiplication equations give IsMonHom. These yield
IsRingHom. No separate negation equation is required for IsRingHom.
(blueprint: lem-weil-pbc-ring-adjunct-preserves-operations) -/
theorem ringAdjunctPreservesOperations
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
    ∀ (X : CommRingObjCat A) (Y : CommRingObjCat B) (f : LF.obj X ⟶ Y),
      IsRingHom (show X.X ⟶ (RF.obj Y).X from adj.homEquiv X.X Y.X
        ((eqToIso hL).inv.app X ≫ f.hom) ≫ (eqToIso hR).inv.app Y) := by
  intro X Y f
  let eL : (LF.obj X).X ≅ L.obj X.X := (eqToIso hL).app X
  let eR : (RF.obj Y).X ≅ R.obj Y.X := (eqToIso hR).app Y
  let g : L.obj X.X ⟶ Y.X := eL.inv ≫ f.hom
  let a : X.X ⟶ R.obj Y.X := adj.homEquiv _ _ g
  have hp : adj.homEquiv (X.X ⊗ X.X) (Y.X ⊗ Y.X)
      ((prodComparisonIso L X.X X.X).hom ≫ (g ⊗ₘ g)) =
      (a ⊗ₘ a) ≫ (prodComparisonIso R Y.X Y.X).inv := by
    apply (cancel_mono (prodComparisonIso R Y.X Y.X).hom).1
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simp only [prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_fst]
      rw [← adj.homEquiv_naturality_right]
      simp only [Category.assoc, tensorHom_fst,
        CartesianMonoidalCategory.prodComparison_fst_assoc]
      rw [adj.homEquiv_naturality_left]
    · simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simp only [prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_snd]
      rw [← adj.homEquiv_naturality_right]
      simp only [Category.assoc, tensorHom_snd,
        CartesianMonoidalCategory.prodComparison_snd_assoc]
      rw [adj.homEquiv_naturality_left]
  have hb (mX : X.X ⊗ X.X ⟶ X.X)
      (mLX : (LF.obj X).X ⊗ (LF.obj X).X ⟶ (LF.obj X).X)
      (mY : Y.X ⊗ Y.X ⟶ Y.X)
      (mRY : (RF.obj Y).X ⊗ (RF.obj Y).X ⟶ (RF.obj Y).X)
      (hl : mLX ≫ eL.hom = (eL.hom ⊗ₘ eL.hom) ≫
        (prodComparisonIso L X.X X.X).inv ≫ L.map mX)
      (hr : mRY ≫ eR.hom = (eR.hom ⊗ₘ eR.hom) ≫
        (prodComparisonIso R Y.X Y.X).inv ≫ R.map mY)
      (hf : mLX ≫ f.hom = (f.hom ⊗ₘ f.hom) ≫ mY) :
      mX ≫ (a ≫ eR.inv) = ((a ≫ eR.inv) ⊗ₘ (a ≫ eR.inv)) ≫ mRY := by
    have hl' : L.map mX ≫ g =
        (prodComparisonIso L X.X X.X).hom ≫ (g ⊗ₘ g) ≫ mY := by
      apply (cancel_epi ((eL.hom ⊗ₘ eL.hom) ≫
        (prodComparisonIso L X.X X.X).inv)).1
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have hlg := congrArg (fun k ↦ k ≫ g) hl
      simp only [Category.assoc] at hlg
      rw [← hlg]
      simp [g, ← Category.assoc, tensorHom_comp_tensorHom, ← hf]
    have ha : mX ≫ a = (a ⊗ₘ a) ≫
        (prodComparisonIso R Y.X Y.X).inv ≫ R.map mY := by
      rw [← adj.homEquiv_naturality_left, hl', ← Category.assoc,
        adj.homEquiv_naturality_right, hp]
      simp only [Category.assoc]
    apply (cancel_mono eR.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hr, ha]
    have htensor : ((a ≫ eR.inv) ⊗ₘ (a ≫ eR.inv)) ≫
        (eR.hom ⊗ₘ eR.hom) = (a ⊗ₘ a) := by
      simp only [tensorHom_comp_tensorHom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    simpa only [Category.assoc] using
      (congrArg (fun k ↦ k ≫ (prodComparisonIso R Y.X Y.X).inv ≫ R.map mY)
        htensor).symm
  have hc (qX : 𝟙_ A ⟶ X.X) (qLX : 𝟙_ B ⟶ (LF.obj X).X)
      (qY : 𝟙_ B ⟶ Y.X) (qRY : 𝟙_ A ⟶ (RF.obj Y).X)
      (hl : qLX ≫ eL.hom = (preservesTerminalIso L).inv ≫ L.map qX)
      (hr : qRY ≫ eR.hom = (preservesTerminalIso R).inv ≫ R.map qY)
      (hf : qLX ≫ f.hom = qY) : qX ≫ (a ≫ eR.inv) = qRY := by
    have hl' : L.map qX ≫ g = (preservesTerminalIso L).hom ≫ qY := by
      apply (cancel_epi (preservesTerminalIso L).inv).1
      simp only [Iso.inv_hom_id_assoc]
      rw [← Category.assoc, ← hl]
      simp [g, hf]
    have ht : adj.homEquiv (𝟙_ A) (𝟙_ B) (preservesTerminalIso L).hom =
        (preservesTerminalIso R).inv := by
      apply (cancel_mono (preservesTerminalIso R).hom).1
      exact isTerminalTensorUnit.hom_ext _ _
    apply (cancel_mono eR.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hr]
    dsimp only [a]
    rw [← adj.homEquiv_naturality_left, hl', adj.homEquiv_naturality_right, ht]
  refine { zero_hom := ?_, add_hom := ?_, one_hom := ?_, mul_hom := ?_ }
  · exact hc _ _ _ _ (opsL X).2.1 (opsR Y).2.1 (IsAddMonHom.zero_hom f.hom)
  · exact hb _ _ _ _ (opsL X).1 (opsR Y).1 (IsAddMonHom.add_hom f.hom)
  · exact hc _ _ _ _ (opsL X).2.2.2.2 (opsR Y).2.2.2.2 (IsMonHom.one_hom f.hom)
  · exact hb _ _ _ _ (opsL X).2.2.2.1 (opsR Y).2.2.2.1 (IsMonHom.mul_hom f.hom)

end CategoryTheory.Adjunction
