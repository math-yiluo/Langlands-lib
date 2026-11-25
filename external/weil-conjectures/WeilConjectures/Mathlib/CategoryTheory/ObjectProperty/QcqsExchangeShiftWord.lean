/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.Algebra.Group.Int.Defs

/-! The canonical four-factor exchange on full subcategories and its shift compatibility.
(blueprint: new-h3-qcqs-exchange-shift-word). -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory.ObjectProperty

private theorem comp_commShift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G H : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    {α : F ⟶ G} {β : G ⟶ H}
    (hα : NatTrans.CommShift α ℤ) (hβ : NatTrans.CommShift β ℤ) :
    NatTrans.CommShift (α ≫ β) ℤ := by
  have := hα
  have := hβ
  infer_instance

-- This is a real transformation built from the canonical inclusion isomorphisms.
/-- The four-factor exchange, transported through full-subcategory inclusions.
Source: normalized compact-support exchange, Step 5
(blueprint: new-h3-qcqs-exchange-shift-word). -/
def exchangeWord
    {C₀ D₀ : Type*} [catC₀ : Category C₀] [catD₀ : Category D₀]
    (P : ObjectProperty C₀) (Q : ObjectProperty D₀)
    (F G : C₀ ⥤ D₀) (A Pa : C₀ ⥤ C₀) (B Pb : D₀ ⥤ D₀)
    (xa : Pa ≅ A) (xb : Pb ≅ B)
    (pF : ∀ K : P.FullSubcategory, Q (F.obj K.obj))
    (pA : ∀ K : P.FullSubcategory, P (A.obj K.obj))
    (pB : ∀ K : Q.FullSubcategory, Q (B.obj K.obj))
    (σ : F ⋙ Pb ⟶ Pa ⋙ G) (ρ : P.ι ⋙ G ≅ P.ι ⋙ F) :
    let T := Q.lift (P.ι ⋙ F) pF
    let a := P.lift (P.ι ⋙ A) pA
    let b := Q.lift (Q.ι ⋙ B) pB
    (T ⋙ b) ⋙ Q.ι ⟶ (a ⋙ T) ⋙ Q.ι := by
  intro T a b
  let ea : a ⋙ P.ι ≅ P.ι ⋙ A := P.liftCompιIso _ pA
  let eb : b ⋙ Q.ι ≅ Q.ι ⋙ B := Q.liftCompιIso _ pB
  let ec : T ⋙ Q.ι ≅ P.ι ⋙ F := Q.liftCompιIso _ pF
  let I := P.ι
  let J := Q.ι
  exact
    (Functor.associator T b J).hom ≫
      Functor.whiskerLeft T eb.hom ≫
      (Functor.associator T J B).inv ≫
      Functor.whiskerRight ec.hom B ≫
      (Functor.associator I F B).hom ≫
      Functor.whiskerLeft I (Functor.whiskerLeft F xb.inv) ≫
      Functor.whiskerLeft I σ ≫
      (Functor.associator I Pa G).inv ≫
      Functor.whiskerRight (Functor.whiskerLeft I xa.hom) G ≫
      Functor.whiskerRight ea.inv G ≫
      (Functor.associator a I G).hom ≫
      Functor.whiskerLeft a ρ.hom ≫
      Functor.whiskerLeft a ec.inv ≫
      (Functor.associator a T J).inv

/-- The transported exchange has exactly the specified four-factor component.
Proof: all full-subcategory comparison maps and associators are identities on objects;
simplifying these identity factors leaves the inverse pullback comparison, the square
exchange, the mapped source comparison and the refinement comparison, in that order.
Source: normalized compact-support exchange, Step 5
(blueprint: new-h3-qcqs-exchange-shift-word). -/
theorem exchangeWord_app
    {C₀ D₀ : Type*} [catC₀ : Category C₀] [catD₀ : Category D₀]
    (P : ObjectProperty C₀) (Q : ObjectProperty D₀)
    (F G : C₀ ⥤ D₀) (A Pa : C₀ ⥤ C₀) (B Pb : D₀ ⥤ D₀)
    (xa : Pa ≅ A) (xb : Pb ≅ B)
    (pF : ∀ K : P.FullSubcategory, Q (F.obj K.obj))
    (pA : ∀ K : P.FullSubcategory, P (A.obj K.obj))
    (pB : ∀ K : Q.FullSubcategory, Q (B.obj K.obj))
    (σ : F ⋙ Pb ⟶ Pa ⋙ G) (ρ : P.ι ⋙ G ≅ P.ι ⋙ F) :
    let a := P.lift (P.ι ⋙ A) pA
    ∀ K : P.FullSubcategory,
      (exchangeWord P Q F G A Pa B Pb xa xb pF pA pB σ ρ).app K =
        xb.inv.app (F.obj K.obj) ≫ σ.app K.obj ≫ G.map (xa.hom.app K.obj) ≫
          ρ.hom.app (a.obj K) := by
  intro a K
  simp [exchangeWord, ObjectProperty.liftCompιIso, a, Category.assoc]

/-- An invertible square factor makes the transported exchange invertible.
Proof: each canonical comparison and associator is an isomorphism; whiskering and
composition preserve invertibility, so all fourteen factors are invertible.
Source: normalized compact-support exchange, Step 5
(blueprint: new-h3-qcqs-exchange-shift-word). -/
instance exchangeWord_isIso
    {C₀ D₀ : Type*} [catC₀ : Category C₀] [catD₀ : Category D₀]
    (P : ObjectProperty C₀) (Q : ObjectProperty D₀)
    (F G : C₀ ⥤ D₀) (A Pa : C₀ ⥤ C₀) (B Pb : D₀ ⥤ D₀)
    (xa : Pa ≅ A) (xb : Pb ≅ B)
    (pF : ∀ K : P.FullSubcategory, Q (F.obj K.obj))
    (pA : ∀ K : P.FullSubcategory, P (A.obj K.obj))
    (pB : ∀ K : Q.FullSubcategory, Q (B.obj K.obj))
    (σ : F ⋙ Pb ⟶ Pa ⋙ G) (ρ : P.ι ⋙ G ≅ P.ι ⋙ F) [IsIso σ] :
    IsIso (exchangeWord P Q F G A Pa B Pb xa xb pF pA pB σ ρ) := by
  dsimp only [exchangeWord]
  infer_instance

/-- Compatibility of each factor implies compatibility of the transported exchange.
Proof: the inclusion comparison maps and associators commute with shifts. Whisker the
four given compatible factors and compose these fourteen compatible transformations.
Source: Mathlib shift calculus and normalized exchange, Step 5
(blueprint: new-h3-qcqs-exchange-shift-word). -/
theorem exchangeWord_commShift
    {C₀ D₀ : Type*} [catC₀ : Category C₀] [catD₀ : Category D₀]
    (P : ObjectProperty C₀) (Q : ObjectProperty D₀)
    (F G : C₀ ⥤ D₀) (A Pa : C₀ ⥤ C₀) (B Pb : D₀ ⥤ D₀)
    (xa : Pa ≅ A) (xb : Pb ≅ B)
    (pF : ∀ K : P.FullSubcategory, Q (F.obj K.obj))
    (pA : ∀ K : P.FullSubcategory, P (A.obj K.obj))
    (pB : ∀ K : Q.FullSubcategory, Q (B.obj K.obj))
    (σ : F ⋙ Pb ⟶ Pa ⋙ G) (ρ : P.ι ⋙ G ≅ P.ι ⋙ F)
    [shiftC₀ : HasShift C₀ ℤ] [shiftD₀ : HasShift D₀ ℤ]
    [hP : HasShift P.FullSubcategory ℤ] [hQ : HasShift Q.FullSubcategory ℤ]
    [iP : P.ι.CommShift ℤ] [iQ : Q.ι.CommShift ℤ]
    [_iF : F.CommShift ℤ] [_iG : G.CommShift ℤ]
    [_iA : A.CommShift ℤ] [_iPa : Pa.CommShift ℤ]
    [_iB : B.CommShift ℤ] [_iPb : Pb.CommShift ℤ]
    [_ixa : NatTrans.CommShift xa.hom ℤ] [_ixb : NatTrans.CommShift xb.hom ℤ]
    [_iσ : NatTrans.CommShift σ ℤ] [_iρ : NatTrans.CommShift ρ.hom ℤ] :
    let T := Q.lift (P.ι ⋙ F) pF
    let a := P.lift (P.ι ⋙ A) pA
    let b := Q.lift (Q.ι ⋙ B) pB
    let ea : a ⋙ P.ι ≅ P.ι ⋙ A := P.liftCompιIso _ pA
    let eb : b ⋙ Q.ι ≅ Q.ι ⋙ B := Q.liftCompιIso _ pB
    let ec : T ⋙ Q.ι ≅ P.ι ⋙ F := Q.liftCompιIso _ pF
    ∀ [_iT : T.CommShift ℤ] [_ia : a.CommShift ℤ] [_ib : b.CommShift ℤ]
      [_hea : NatTrans.CommShift ea.hom ℤ] [_heb : NatTrans.CommShift eb.hom ℤ]
      [_hec : NatTrans.CommShift ec.hom ℤ],
      NatTrans.CommShift (exchangeWord P Q F G A Pa B Pb xa xb pF pA pB σ ρ) ℤ := by
  intro T a b ea eb ec _ _ _ hea heb hec
  dsimp only [exchangeWord]
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  apply comp_commShift
  · infer_instance
  infer_instance

end CategoryTheory.ObjectProperty
