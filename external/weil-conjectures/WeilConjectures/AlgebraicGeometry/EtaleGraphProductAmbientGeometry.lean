/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProductInterchange

/-! # Proper ambient part of the product interchange grid

Source: Stacks Project, Tag 0F7J, comparison of the proper projection grids A--F;
the product-graph extension in lem-pur-etale-graph-product-row-pasting.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

namespace EtaleGraphPresentation.ProductRow

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (s t : EtaleGraphPresentation f) (second : Bool)

/-- The selected presentation. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev side := if second then t else s

/-- The selected proper projection. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def projection : (PairwiseProduct.presentation s t).P ⟶ (side s t second).P := by
  cases second
  · exact pullback.fst s.p t.p
  · exact pullback.snd s.p t.p

/-- The morphism property follows from base change or proper-to-separated.
Source: Stacks Tags 01W4, 01W6 and 0F7J
(auxiliary; not a blueprint node). -/
instance projection_proper : IsProper (projection s t second) := by
  cases second <;> dsimp [projection] <;> infer_instance

/-- The selected supporting neighborhood in the ambient product. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev neighborhood := pullback (projection s t second) (side s t second).e

/-- Its open inclusion. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev j : neighborhood s t second ⟶ (PairwiseProduct.presentation s t).P :=
  pullback.fst _ _

/-- Its proper projection onto the selected support. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev q : neighborhood s t second ⟶ (side s t second).U := pullback.snd _ _

/-- Inclusion of the intersection into the selected neighborhood. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def v : (PairwiseProduct.presentation s t).U ⟶ neighborhood s t second := by
  cases second
  · exact PairwiseProduct.v₁ s t
  · exact PairwiseProduct.v₂ s t

/-- The morphism property follows from base change or proper-to-separated.
Source: Stacks Tags 01W4, 01W6 and 0F7J
(auxiliary; not a blueprint node). -/
instance v_open : IsOpenImmersion (v s t second) := by
  cases second
  · exact (PairwiseProduct.geometry s t).openV₁
  · exact (PairwiseProduct.geometry s t).openV₂

/-- The proper graph in the selected neighborhood. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def z : X ⟶ neighborhood s t second := (PairwiseProduct.presentation s t).a ≫ v s t second

/-- The morphism property follows from base change or proper-to-separated.
Source: Stacks Tags 01W4, 01W6 and 0F7J
(auxiliary; not a blueprint node). -/
instance z_proper : IsProper (z s t second) := by
  cases second
  · exact (PairwiseProduct.geometry s t).properZ₁
  · exact (PairwiseProduct.geometry s t).properZ₂

/-- The defining projection equation of the selected neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma z_q : z s t second ≫ q s t second = (side s t second).a := by
  cases second
  · exact (PairwiseProduct.geometry s t).z₁_q
  · exact (PairwiseProduct.geometry s t).z₂_q

/-- The defining projection equation of the selected neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma v_j : v s t second ≫ j s t second = (PairwiseProduct.presentation s t).e := by
  cases second
  · exact (PairwiseProduct.geometry s t).v₁_b
  · exact (PairwiseProduct.geometry s t).v₂_b

/-- The defining projection equation of the selected neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma z_j : z s t second ≫ j s t second =
    (PairwiseProduct.presentation s t).a ≫ (PairwiseProduct.presentation s t).e := by
  simp only [z, Category.assoc, v_j]

/-- The defining projection equation of the selected neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma projection_p : projection s t second ≫ (side s t second).p =
    (PairwiseProduct.presentation s t).p := by
  cases second
  · rfl
  · exact pullback.condition.symm

/-- The presentation before shrinking to the intersection of the supports.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev ambient : EtaleGraphPresentation f where
  U := neighborhood s t second
  P := (PairwiseProduct.presentation s t).P
  a := z s t second
  e := j s t second
  p := (PairwiseProduct.presentation s t).p
  fac := by
    rw [← Category.assoc, z_j]
    exact (PairwiseProduct.presentation s t).fac

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The proper-ambient factor of lambda, with its Cartesian exchange and compositors.
Source: Stacks Tags 0F7C and 0F7J
(auxiliary; not a blueprint node). -/
def ambientLambda : (side s t second).functor A ≅ (ambient s t second).functor A :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (z s t second) (q s t second) _ (z_q s t second)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A
        (IsPullback.of_hasPullback (projection s t second) (side s t second).e).flip) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
          (projection s t second) (side s t second).p _ (projection_p s t second)))

/-- The remaining graph-triangle factor of lambda, followed by the open compositor.
Source: Stacks Tags 0F7D and 0F7J
(auxiliary; not a blueprint node). -/
def shrinkLambda : (ambient s t second).functor A ≅
    (PairwiseProduct.presentation s t).functor A :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
        (PairwiseProduct.presentation s t).a (v s t second) (z s t second) rfl).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
            (v s t second) (j s t second)).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
            (v_j s t second)) _)

/-- The selected lambda with a dependent source. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def lambda : (side s t second).functor A ≅ (PairwiseProduct.presentation s t).functor A := by
  cases second
  · exact PairwiseProduct.lambda₁ s t A
  · exact PairwiseProduct.lambda₂ s t A

/-- Lambda is the proper-ambient factor followed by its graph-triangle factor.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma lambda_factor : lambda s t second A =
    ambientLambda s t second A ≪≫ shrinkLambda s t second A := by
  cases second <;>
    simp only [lambda, PairwiseProduct.lambda₁, PairwiseProduct.lambda₂,
      etaleProductGraphLambda, ambientLambda, shrinkLambda, projection, side, q, j, z, v,
      ambient, PairwiseProduct.presentation, PairwiseProduct.z₁, PairwiseProduct.z₂,
      Bool.false_eq_true, ↓reduceIte, Iso.trans_assoc] <;> rfl

end EtaleGraphPresentation.ProductRow

namespace EtaleGraphInterchangeDiagram.ProductRow.First

open EtaleGraphPresentation

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (d₁ d₂ : EtaleGraphInterchangeDiagram f g)

/-- The selected diagram. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev d : EtaleGraphInterchangeDiagram f g := (d₁, d₂).1

/-- Source neighborhood presentation. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev F := EtaleGraphPresentation.ProductRow.ambient
  d₁.sourcePresentation d₂.sourcePresentation false

/-- Middle neighborhood presentation. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev G := EtaleGraphPresentation.ProductRow.ambient
  (ofCompactification d₁.compactification) (ofCompactification d₂.compactification) false

/-- Composite neighborhood presentation. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev H := EtaleGraphPresentation.ProductRow.ambient
  d₁.compositePresentation d₂.compositePresentation false

/-- Projection of the source ambient product. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev prF := EtaleGraphPresentation.ProductRow.projection
  d₁.sourcePresentation d₂.sourcePresentation false

/-- Projection of the middle ambient product. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev prG := EtaleGraphPresentation.ProductRow.projection
  (ofCompactification d₁.compactification) (ofCompactification d₂.compactification) false

/-- Projection of the composite ambient product. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev prH := EtaleGraphPresentation.ProductRow.projection
  d₁.compositePresentation d₂.compositePresentation false

/-- The intermediate open neighborhood V_selected times P_other over Z.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev N := pullback (prH d₁ d₂) (d d₁ d₂).k

/-- Its open inclusion in the composite ambient product. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev K : N d₁ d₂ ⟶ (d₁.productH d₂).P := pullback.fst _ _

/-- Its proper projection onto V_selected. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev qN : N d₁ d₂ ⟶ (d d₁ d₂).V := pullback.snd _ _

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma productP_projection :
    d₁.productP d₂ ≫ prG d₁ d₂ = prH d₁ d₂ ≫ (d d₁ d₂).p := by
    simp [prG, prH, EtaleGraphPresentation.ProductRow.projection, d, productP,
      compactification, compositePresentation, ofCompactification,
      PairwiseProduct.presentation, pullback.map]

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma productBV_K_projection :
    d₁.productBV d₂ ≫ d₁.productK d₂ ≫ prH d₁ d₂ =
      prF d₁ d₂ ≫ (d d₁ d₂).k := by
    simp [prF, prH, EtaleGraphPresentation.ProductRow.projection, d, productBV, productK,
      sourcePresentation, compositePresentation, PairwiseProduct.presentation, pullback.map]

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma prF_r : prF d₁ d₂ ≫ (d d₁ d₂).r = (d₁.productF d₂).p := by
  rfl

/-- The product of e_selected with the identity on the other proper ambient factor.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def E : (H d₁ d₂).U ⟶ N d₁ d₂ := by
  change pullback (prH d₁ d₂) ((d d₁ d₂).e ≫ (d d₁ d₂).k) ⟶
    pullback (prH d₁ d₂) (d d₁ d₂).k
  exact pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (d d₁ d₂).e)
    ((pullback.condition (f := prH d₁ d₂)
      (g := (d d₁ d₂).e ≫ (d d₁ d₂).k)).trans (Category.assoc _ _ _).symm)

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma E_K : E d₁ d₂ ≫ K d₁ d₂ = (H d₁ d₂).e := by
  simp only [E, id_eq, K, pullback.lift_fst]
  rfl

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma E_qN : E d₁ d₂ ≫ qN d₁ d₂ =
    EtaleGraphPresentation.ProductRow.q
      d₁.compositePresentation d₂.compositePresentation false ≫ (d d₁ d₂).e := by
  simp only [E, id_eq, qN, pullback.lift_snd]
  rfl

/-- The morphism property follows from base change or proper-to-separated.
Source: Stacks Tags 01W4, 01W6 and 0F7J
(auxiliary; not a blueprint node). -/
instance E_open : IsOpenImmersion (E d₁ d₂) := by
  have : IsOpenImmersion (E d₁ d₂ ≫ K d₁ d₂) := by
    have h := (H d₁ d₂).openE
    simp only [E, id_eq, K, pullback.lift_fst]
    exact h
  exact IsOpenImmersion.of_comp _ (K d₁ d₂)

/-- The proper vertical map from the mixed neighborhood to the middle neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def R : N d₁ d₂ ⟶ (G d₁ d₂).U :=
  pullback.lift (K d₁ d₂ ≫ d₁.productP d₂)
    (qN d₁ d₂ ≫ (d d₁ d₂).r) (by
      rw [Category.assoc, productP_projection, ← Category.assoc, pullback.condition,
        Category.assoc, (d d₁ d₂).square.w, Category.assoc]
      rfl)

/-- The morphism property follows from base change or proper-to-separated.
Source: Stacks Tags 01W4, 01W6 and 0F7J
(auxiliary; not a blueprint node). -/
instance R_proper : IsProper (R d₁ d₂) := by
  have : IsProper (R d₁ d₂ ≫ EtaleGraphPresentation.ProductRow.q
      (ofCompactification d₁.compactification) (ofCompactification d₂.compactification)
      false) := by
    dsimp [R]
    rw [pullback.lift_snd]
    infer_instance
  exact IsProper.of_comp _ (EtaleGraphPresentation.ProductRow.q
    (ofCompactification d₁.compactification) (ofCompactification d₂.compactification)
    false)

/-- Proper inclusion of the product over Y into the mixed ambient neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def BV : (F d₁ d₂).P ⟶ N d₁ d₂ :=
  pullback.lift (d₁.productBV d₂ ≫ d₁.productK d₂) (prF d₁ d₂)
    (by simpa only [Category.assoc] using productBV_K_projection d₁ d₂)

/-- The morphism property follows from base change or proper-to-separated.
Source: Stacks Tags 01W4, 01W6 and 0F7J
(auxiliary; not a blueprint node). -/
instance BV_proper : IsProper (BV d₁ d₂) := by
  have : IsProper (BV d₁ d₂ ≫ qN d₁ d₂) := by
    simpa only [BV, pullback.lift_snd] using
      (EtaleGraphPresentation.ProductRow.projection_proper
        d₁.sourcePresentation d₂.sourcePresentation false)
  exact IsProper.of_comp _ (qN d₁ d₂)

/-- Proper map from the source neighborhood to the composite neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def BW : (F d₁ d₂).U ⟶ (H d₁ d₂).U :=
  pullback.lift ((F d₁ d₂).e ≫ d₁.productBV d₂ ≫ d₁.productK d₂)
    (EtaleGraphPresentation.ProductRow.q
      d₁.sourcePresentation d₂.sourcePresentation false) (by
      rw [Category.assoc, Category.assoc, productBV_K_projection,
        ← Category.assoc, pullback.condition, Category.assoc]
      rfl)

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma BW_e : BW d₁ d₂ ≫ (H d₁ d₂).e =
    (F d₁ d₂).e ≫ d₁.productBV d₂ ≫ d₁.productK d₂ := by
  exact pullback.lift_fst _ _ _

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma BW_q : BW d₁ d₂ ≫ EtaleGraphPresentation.ProductRow.q
      d₁.compositePresentation d₂.compositePresentation false =
    EtaleGraphPresentation.ProductRow.q
      d₁.sourcePresentation d₂.sourcePresentation false := by
  exact pullback.lift_snd _ _ _

/-- The morphism property follows from base change or proper-to-separated.
Source: Stacks Tags 01W4, 01W6 and 0F7J
(auxiliary; not a blueprint node). -/
instance BW_proper : IsProper (BW d₁ d₂) := by
  have : IsProper (BW d₁ d₂ ≫ EtaleGraphPresentation.ProductRow.q
      d₁.compositePresentation d₂.compositePresentation false) := by
    simpa only [BW, pullback.lift_snd] using
      (inferInstance : IsProper (EtaleGraphPresentation.ProductRow.q
        d₁.sourcePresentation d₂.sourcePresentation false))
  exact IsProper.of_comp _ (EtaleGraphPresentation.ProductRow.q
    d₁.compositePresentation d₂.compositePresentation false)

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma a_BW : (F d₁ d₂).a ≫ BW d₁ d₂ = (H d₁ d₂).a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, BW, pullback.lift_fst]
    change EtaleGraphPresentation.ProductRow.z
        d₁.sourcePresentation d₂.sourcePresentation false ≫
        EtaleGraphPresentation.ProductRow.j
          d₁.sourcePresentation d₂.sourcePresentation false ≫
        d₁.productBV d₂ ≫ d₁.productK d₂ =
      EtaleGraphPresentation.ProductRow.z
        d₁.compositePresentation d₂.compositePresentation false ≫
        EtaleGraphPresentation.ProductRow.j
          d₁.compositePresentation d₂.compositePresentation false
    rw [← Category.assoc, EtaleGraphPresentation.ProductRow.z_j,
      EtaleGraphPresentation.ProductRow.z_j]
    calc
      _ = (d₁.productF d₂).a ≫
          ((d₁.productF d₂).e ≫ d₁.productBV d₂) ≫ d₁.productK d₂ := by
        simp only [Category.assoc]
      _ = (d₁.productF d₂).a ≫
          (d₁.productBW d₂ ≫ d₁.productE d₂) ≫ d₁.productK d₂ := by
        rw [(d₁.productB_square d₂).w]
      _ = ((d₁.productF d₂).a ≫ d₁.productBW d₂) ≫
          (d₁.productE d₂ ≫ d₁.productK d₂) := by simp only [Category.assoc]
      _ = _ := by rw [d₁.productA_productBW d₂, d₁.productE_productK d₂]
  · simp only [Category.assoc, BW, pullback.lift_snd]
    exact (EtaleGraphPresentation.ProductRow.z_q
      d₁.sourcePresentation d₂.sourcePresentation false).trans
      (EtaleGraphPresentation.ProductRow.z_q
        d₁.compositePresentation d₂.compositePresentation false).symm

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma BV_R : BV d₁ d₂ ≫ R d₁ d₂ =
    (F d₁ d₂).p ≫ (G d₁ d₂).a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, R, pullback.lift_fst, BV, pullback.lift_fst_assoc]
    rw [(d₁.product_square d₂).w, ← Category.assoc,
      d₁.productBV_productR d₂]
    change _ = (d₁.productF d₂).p ≫ EtaleGraphPresentation.ProductRow.z _ _ _ ≫
      EtaleGraphPresentation.ProductRow.j _ _ _
    rw [EtaleGraphPresentation.ProductRow.z_j]
    simp only [Category.assoc]
  · simp only [Category.assoc, R, pullback.lift_snd, BV, pullback.lift_snd_assoc]
    rw [prF_r]
    change _ = (d₁.productF d₂).p ≫ EtaleGraphPresentation.ProductRow.z _ _ _ ≫
      EtaleGraphPresentation.ProductRow.q _ _ _
    rw [EtaleGraphPresentation.ProductRow.z_q]
    simp [EtaleGraphPresentation.ProductRow.side, ofCompactification]

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma B_square : CommSq (F d₁ d₂).e (BW d₁ d₂)
    (BV d₁ d₂) (E d₁ d₂) := by
  constructor
  apply pullback.hom_ext
  · change ((F d₁ d₂).e ≫ BV d₁ d₂) ≫ K d₁ d₂ =
      (BW d₁ d₂ ≫ E d₁ d₂) ≫ K d₁ d₂
    calc
      _ = (F d₁ d₂).e ≫ d₁.productBV d₂ ≫ d₁.productK d₂ := by
        simp only [Category.assoc, BV, K, pullback.lift_fst]
      _ = BW d₁ d₂ ≫ (H d₁ d₂).e := (BW_e d₁ d₂).symm
      _ = _ := by rw [Category.assoc, E_K]
  · change ((F d₁ d₂).e ≫ BV d₁ d₂) ≫ qN d₁ d₂ =
      (BW d₁ d₂ ≫ E d₁ d₂) ≫ qN d₁ d₂
    calc
      _ = (F d₁ d₂).e ≫ prF d₁ d₂ := by
        simp only [Category.assoc, BV, qN, pullback.lift_snd]
      _ = EtaleGraphPresentation.ProductRow.q
          d₁.sourcePresentation d₂.sourcePresentation false ≫ (d d₁ d₂).e :=
        pullback.condition
      _ = _ := by rw [Category.assoc, E_qN, ← Category.assoc, BW_q]

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma Q_square : CommSq (K d₁ d₂) (R d₁ d₂)
    (d₁.productP d₂) (G d₁ d₂).e := by
  constructor
  simp only [R, pullback.lift_fst]

/-- The intermediate source word over the middle supporting neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev F₀ (A : Type (u + 1)) [CommRing A] :=
  R(((H d₁ d₂).a)_*[ModuleCat.{u + 1} A]) ⋙
    D((E d₁ d₂)_!open[ModuleCat.{u + 1} A]) ⋙
      R((R d₁ d₂)_*[ModuleCat.{u + 1} A])

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The inverse B exchange for the proper ambient neighborhoods.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def liftInterchange :
    (F d₁ d₂).functor A ⋙ R(((G d₁ d₂).a)_*[ModuleCat.{u + 1} A]) ≅
      F₀ d₁ d₂ A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
          (F d₁ d₂).p (G d₁ d₂).a
          (BV d₁ d₂ ≫ R d₁ d₂) (BV_R d₁ d₂).symm ≪≫
          (rightDerivedLowerStarComp (ModuleCat.{u + 1} A)
            (BV d₁ d₂) (R d₁ d₂)).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (etaleGraphNormalizedProperOpenExchange A (F d₁ d₂).e
          (BW d₁ d₂) (BV d₁ d₂) (E d₁ d₂)
          (B_square d₁ d₂)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (F d₁ d₂).a (BW d₁ d₂) (H d₁ d₂).a
        (a_BW d₁ d₂)) _

/-- The Q exchange for the proper ambient neighborhoods.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def squareInterchange :
    F₀ d₁ d₂ A ⋙
        (D(((G d₁ d₂).e)_!open[ModuleCat.{u + 1} A]) ⋙
          R(((G d₁ d₂).p)_*[ModuleCat.{u + 1} A])) ≅
      (H d₁ d₂).functor A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (etaleGraphNormalizedProperOpenExchange A (K d₁ d₂)
            (R d₁ d₂) (d₁.productP d₂) (G d₁ d₂).e
            (Q_square d₁ d₂)) _ ≪≫
        Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
          (E d₁ d₂) (K d₁ d₂)).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
            (E_K d₁ d₂)) _ ≪≫
      Functor.isoWhiskerLeft _
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
          (d₁.productP d₂) (G d₁ d₂).p (H d₁ d₂).p
          (d₁.productP_productQ d₂)))

/-- The fixed common boundary at the three proper ambient neighborhoods.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def interchange : (F d₁ d₂).functor A ⋙ (G d₁ d₂).functor A ≅
    (H d₁ d₂).functor A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (liftInterchange d₁ d₂ A) _ ≪≫
    squareInterchange d₁ d₂ A

end EtaleGraphInterchangeDiagram.ProductRow.First

namespace EtaleGraphInterchangeDiagram.ProductRow.Second

open EtaleGraphPresentation

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (d₁ d₂ : EtaleGraphInterchangeDiagram f g)

/-- The selected diagram. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev d : EtaleGraphInterchangeDiagram f g := (d₁, d₂).2

/-- Source neighborhood presentation. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev F := EtaleGraphPresentation.ProductRow.ambient
  d₁.sourcePresentation d₂.sourcePresentation true

/-- Middle neighborhood presentation. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev G := EtaleGraphPresentation.ProductRow.ambient
  (ofCompactification d₁.compactification) (ofCompactification d₂.compactification) true

/-- Composite neighborhood presentation. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev H := EtaleGraphPresentation.ProductRow.ambient
  d₁.compositePresentation d₂.compositePresentation true

/-- Projection of the source ambient product. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev prF := EtaleGraphPresentation.ProductRow.projection
  d₁.sourcePresentation d₂.sourcePresentation true

/-- Projection of the middle ambient product. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev prG := EtaleGraphPresentation.ProductRow.projection
  (ofCompactification d₁.compactification) (ofCompactification d₂.compactification) true

/-- Projection of the composite ambient product. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev prH := EtaleGraphPresentation.ProductRow.projection
  d₁.compositePresentation d₂.compositePresentation true

/-- The intermediate open neighborhood V_selected times P_other over Z.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev N := pullback (prH d₁ d₂) (d d₁ d₂).k

/-- Its open inclusion in the composite ambient product. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev K : N d₁ d₂ ⟶ (d₁.productH d₂).P := pullback.fst _ _

/-- Its proper projection onto V_selected. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev qN : N d₁ d₂ ⟶ (d d₁ d₂).V := pullback.snd _ _

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma productP_projection :
    d₁.productP d₂ ≫ prG d₁ d₂ = prH d₁ d₂ ≫ (d d₁ d₂).p := by
    simp [prG, prH, EtaleGraphPresentation.ProductRow.projection, d, productP,
      compactification, compositePresentation, ofCompactification,
      PairwiseProduct.presentation, pullback.map]

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma productBV_K_projection :
    d₁.productBV d₂ ≫ d₁.productK d₂ ≫ prH d₁ d₂ =
      prF d₁ d₂ ≫ (d d₁ d₂).k := by
    simp [prF, prH, EtaleGraphPresentation.ProductRow.projection, d, productBV, productK,
      sourcePresentation, compositePresentation, PairwiseProduct.presentation, pullback.map]

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma prF_r : prF d₁ d₂ ≫ (d d₁ d₂).r = (d₁.productF d₂).p := by
  exact pullback.condition.symm

/-- The product of e_selected with the identity on the other proper ambient factor.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def E : (H d₁ d₂).U ⟶ N d₁ d₂ := by
  change pullback (prH d₁ d₂) ((d d₁ d₂).e ≫ (d d₁ d₂).k) ⟶
    pullback (prH d₁ d₂) (d d₁ d₂).k
  exact pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (d d₁ d₂).e)
    ((pullback.condition (f := prH d₁ d₂)
      (g := (d d₁ d₂).e ≫ (d d₁ d₂).k)).trans (Category.assoc _ _ _).symm)

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma E_K : E d₁ d₂ ≫ K d₁ d₂ = (H d₁ d₂).e := by
  simp only [E, id_eq, K, pullback.lift_fst]
  rfl

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma E_qN : E d₁ d₂ ≫ qN d₁ d₂ =
    EtaleGraphPresentation.ProductRow.q
      d₁.compositePresentation d₂.compositePresentation true ≫ (d d₁ d₂).e := by
  simp only [E, id_eq, qN, pullback.lift_snd]
  rfl

/-- The morphism property follows from base change or proper-to-separated.
Source: Stacks Tags 01W4, 01W6 and 0F7J
(auxiliary; not a blueprint node). -/
instance E_open : IsOpenImmersion (E d₁ d₂) := by
  have : IsOpenImmersion (E d₁ d₂ ≫ K d₁ d₂) := by
    have h := (H d₁ d₂).openE
    simp only [E, id_eq, K, pullback.lift_fst]
    exact h
  exact IsOpenImmersion.of_comp _ (K d₁ d₂)

/-- The proper vertical map from the mixed neighborhood to the middle neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def R : N d₁ d₂ ⟶ (G d₁ d₂).U :=
  pullback.lift (K d₁ d₂ ≫ d₁.productP d₂)
    (qN d₁ d₂ ≫ (d d₁ d₂).r) (by
      rw [Category.assoc, productP_projection, ← Category.assoc, pullback.condition,
        Category.assoc, (d d₁ d₂).square.w, Category.assoc]
      rfl)

/-- The morphism property follows from base change or proper-to-separated.
Source: Stacks Tags 01W4, 01W6 and 0F7J
(auxiliary; not a blueprint node). -/
instance R_proper : IsProper (R d₁ d₂) := by
  have : IsProper (R d₁ d₂ ≫ EtaleGraphPresentation.ProductRow.q
      (ofCompactification d₁.compactification) (ofCompactification d₂.compactification)
      true) := by
    dsimp [R]
    rw [pullback.lift_snd]
    infer_instance
  exact IsProper.of_comp _ (EtaleGraphPresentation.ProductRow.q
    (ofCompactification d₁.compactification) (ofCompactification d₂.compactification)
    true)

/-- Proper inclusion of the product over Y into the mixed ambient neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def BV : (F d₁ d₂).P ⟶ N d₁ d₂ :=
  pullback.lift (d₁.productBV d₂ ≫ d₁.productK d₂) (prF d₁ d₂)
    (by simpa only [Category.assoc] using productBV_K_projection d₁ d₂)

/-- The morphism property follows from base change or proper-to-separated.
Source: Stacks Tags 01W4, 01W6 and 0F7J
(auxiliary; not a blueprint node). -/
instance BV_proper : IsProper (BV d₁ d₂) := by
  have : IsProper (BV d₁ d₂ ≫ qN d₁ d₂) := by
    simpa only [BV, pullback.lift_snd] using
      (EtaleGraphPresentation.ProductRow.projection_proper
        d₁.sourcePresentation d₂.sourcePresentation true)
  exact IsProper.of_comp _ (qN d₁ d₂)

/-- Proper map from the source neighborhood to the composite neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def BW : (F d₁ d₂).U ⟶ (H d₁ d₂).U :=
  pullback.lift ((F d₁ d₂).e ≫ d₁.productBV d₂ ≫ d₁.productK d₂)
    (EtaleGraphPresentation.ProductRow.q
      d₁.sourcePresentation d₂.sourcePresentation true) (by
      rw [Category.assoc, Category.assoc, productBV_K_projection,
        ← Category.assoc, pullback.condition, Category.assoc]
      rfl)

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma BW_e : BW d₁ d₂ ≫ (H d₁ d₂).e =
    (F d₁ d₂).e ≫ d₁.productBV d₂ ≫ d₁.productK d₂ := by
  exact pullback.lift_fst _ _ _

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma BW_q : BW d₁ d₂ ≫ EtaleGraphPresentation.ProductRow.q
      d₁.compositePresentation d₂.compositePresentation true =
    EtaleGraphPresentation.ProductRow.q
      d₁.sourcePresentation d₂.sourcePresentation true := by
  exact pullback.lift_snd _ _ _

/-- The morphism property follows from base change or proper-to-separated.
Source: Stacks Tags 01W4, 01W6 and 0F7J
(auxiliary; not a blueprint node). -/
instance BW_proper : IsProper (BW d₁ d₂) := by
  have : IsProper (BW d₁ d₂ ≫ EtaleGraphPresentation.ProductRow.q
      d₁.compositePresentation d₂.compositePresentation true) := by
    simpa only [BW, pullback.lift_snd] using
      (inferInstance : IsProper (EtaleGraphPresentation.ProductRow.q
        d₁.sourcePresentation d₂.sourcePresentation true))
  exact IsProper.of_comp _ (EtaleGraphPresentation.ProductRow.q
    d₁.compositePresentation d₂.compositePresentation true)

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma a_BW : (F d₁ d₂).a ≫ BW d₁ d₂ = (H d₁ d₂).a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, BW, pullback.lift_fst]
    change EtaleGraphPresentation.ProductRow.z
        d₁.sourcePresentation d₂.sourcePresentation true ≫
        EtaleGraphPresentation.ProductRow.j
          d₁.sourcePresentation d₂.sourcePresentation true ≫
        d₁.productBV d₂ ≫ d₁.productK d₂ =
      EtaleGraphPresentation.ProductRow.z
        d₁.compositePresentation d₂.compositePresentation true ≫
        EtaleGraphPresentation.ProductRow.j
          d₁.compositePresentation d₂.compositePresentation true
    rw [← Category.assoc, EtaleGraphPresentation.ProductRow.z_j,
      EtaleGraphPresentation.ProductRow.z_j]
    calc
      _ = (d₁.productF d₂).a ≫
          ((d₁.productF d₂).e ≫ d₁.productBV d₂) ≫ d₁.productK d₂ := by
        simp only [Category.assoc]
      _ = (d₁.productF d₂).a ≫
          (d₁.productBW d₂ ≫ d₁.productE d₂) ≫ d₁.productK d₂ := by
        rw [(d₁.productB_square d₂).w]
      _ = ((d₁.productF d₂).a ≫ d₁.productBW d₂) ≫
          (d₁.productE d₂ ≫ d₁.productK d₂) := by simp only [Category.assoc]
      _ = _ := by rw [d₁.productA_productBW d₂, d₁.productE_productK d₂]
  · simp only [Category.assoc, BW, pullback.lift_snd]
    exact (EtaleGraphPresentation.ProductRow.z_q
      d₁.sourcePresentation d₂.sourcePresentation true).trans
      (EtaleGraphPresentation.ProductRow.z_q
        d₁.compositePresentation d₂.compositePresentation true).symm

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma BV_R : BV d₁ d₂ ≫ R d₁ d₂ =
    (F d₁ d₂).p ≫ (G d₁ d₂).a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, R, pullback.lift_fst, BV, pullback.lift_fst_assoc]
    rw [(d₁.product_square d₂).w, ← Category.assoc,
      d₁.productBV_productR d₂]
    change _ = (d₁.productF d₂).p ≫ EtaleGraphPresentation.ProductRow.z _ _ _ ≫
      EtaleGraphPresentation.ProductRow.j _ _ _
    rw [EtaleGraphPresentation.ProductRow.z_j]
    simp only [Category.assoc]
  · simp only [Category.assoc, R, pullback.lift_snd, BV, pullback.lift_snd_assoc]
    rw [prF_r]
    change _ = (d₁.productF d₂).p ≫ EtaleGraphPresentation.ProductRow.z _ _ _ ≫
      EtaleGraphPresentation.ProductRow.q _ _ _
    rw [EtaleGraphPresentation.ProductRow.z_q]
    simp [EtaleGraphPresentation.ProductRow.side, ofCompactification]

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma B_square : CommSq (F d₁ d₂).e (BW d₁ d₂)
    (BV d₁ d₂) (E d₁ d₂) := by
  constructor
  apply pullback.hom_ext
  · change ((F d₁ d₂).e ≫ BV d₁ d₂) ≫ K d₁ d₂ =
      (BW d₁ d₂ ≫ E d₁ d₂) ≫ K d₁ d₂
    calc
      _ = (F d₁ d₂).e ≫ d₁.productBV d₂ ≫ d₁.productK d₂ := by
        simp only [Category.assoc, BV, K, pullback.lift_fst]
      _ = BW d₁ d₂ ≫ (H d₁ d₂).e := (BW_e d₁ d₂).symm
      _ = _ := by rw [Category.assoc, E_K]
  · change ((F d₁ d₂).e ≫ BV d₁ d₂) ≫ qN d₁ d₂ =
      (BW d₁ d₂ ≫ E d₁ d₂) ≫ qN d₁ d₂
    calc
      _ = (F d₁ d₂).e ≫ prF d₁ d₂ := by
        simp only [Category.assoc, BV, qN, pullback.lift_snd]
      _ = EtaleGraphPresentation.ProductRow.q
          d₁.sourcePresentation d₂.sourcePresentation true ≫ (d d₁ d₂).e :=
        pullback.condition
      _ = _ := by rw [Category.assoc, E_qN, ← Category.assoc, BW_q]

/-- The defining projection identity of the ambient grid. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma Q_square : CommSq (K d₁ d₂) (R d₁ d₂)
    (d₁.productP d₂) (G d₁ d₂).e := by
  constructor
  simp only [R, pullback.lift_fst]

/-- The intermediate source word over the middle supporting neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev F₀ (A : Type (u + 1)) [CommRing A] :=
  R(((H d₁ d₂).a)_*[ModuleCat.{u + 1} A]) ⋙
    D((E d₁ d₂)_!open[ModuleCat.{u + 1} A]) ⋙
      R((R d₁ d₂)_*[ModuleCat.{u + 1} A])

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The inverse B exchange for the proper ambient neighborhoods.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def liftInterchange :
    (F d₁ d₂).functor A ⋙ R(((G d₁ d₂).a)_*[ModuleCat.{u + 1} A]) ≅
      F₀ d₁ d₂ A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
          (F d₁ d₂).p (G d₁ d₂).a
          (BV d₁ d₂ ≫ R d₁ d₂) (BV_R d₁ d₂).symm ≪≫
          (rightDerivedLowerStarComp (ModuleCat.{u + 1} A)
            (BV d₁ d₂) (R d₁ d₂)).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (etaleGraphNormalizedProperOpenExchange A (F d₁ d₂).e
          (BW d₁ d₂) (BV d₁ d₂) (E d₁ d₂)
          (B_square d₁ d₂)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (F d₁ d₂).a (BW d₁ d₂) (H d₁ d₂).a
        (a_BW d₁ d₂)) _

/-- The Q exchange for the proper ambient neighborhoods.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def squareInterchange :
    F₀ d₁ d₂ A ⋙
        (D(((G d₁ d₂).e)_!open[ModuleCat.{u + 1} A]) ⋙
          R(((G d₁ d₂).p)_*[ModuleCat.{u + 1} A])) ≅
      (H d₁ d₂).functor A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (etaleGraphNormalizedProperOpenExchange A (K d₁ d₂)
            (R d₁ d₂) (d₁.productP d₂) (G d₁ d₂).e
            (Q_square d₁ d₂)) _ ≪≫
        Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
          (E d₁ d₂) (K d₁ d₂)).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
            (E_K d₁ d₂)) _ ≪≫
      Functor.isoWhiskerLeft _
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
          (d₁.productP d₂) (G d₁ d₂).p (H d₁ d₂).p
          (d₁.productP_productQ d₂)))

/-- The fixed common boundary at the three proper ambient neighborhoods.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def interchange : (F d₁ d₂).functor A ⋙ (G d₁ d₂).functor A ≅
    (H d₁ d₂).functor A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (liftInterchange d₁ d₂ A) _ ≪≫
    squareInterchange d₁ d₂ A

end EtaleGraphInterchangeDiagram.ProductRow.Second

namespace EtaleGraphInterchangeDiagram.ProductRow

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/-- The square part of the supplied interchange, before adjoining the identity graph.
Source: Stacks Tag 0F7J, the first calculation in the proof of composition
(auxiliary; not a blueprint node). -/
def rawSquare (A : Type (u + 1)) [CommRing A] [Finite A]
    (d : EtaleGraphInterchangeDiagram f g) :
    d.sourcePresentation.functor A ⋙
        (D((d.i)_!open[ModuleCat.{u + 1} A]) ⋙ R((d.q)_*[ModuleCat.{u + 1} A])) ≅
      d.compositePresentation.functor A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R((d.a)_*[ModuleCat.{u + 1} A])
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft D((d.e)_!open[ModuleCat.{u + 1} A])
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              (etaleGraphNormalizedProperOpenExchange A d.k d.r d.p d.i d.square)
              R((d.q)_*[ModuleCat.{u + 1} A]) ≪≫
            Functor.associator _ _ _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) d.e d.k).symm
          (R((d.p)_*[ModuleCat.{u + 1} A]) ⋙ R((d.q)_*[ModuleCat.{u + 1} A])) ≪≫
        Functor.isoWhiskerLeft D((d.e ≫ d.k)_!open[ModuleCat.{u + 1} A])
          (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) d.p d.q))

end EtaleGraphInterchangeDiagram.ProductRow

namespace EtaleGraphInterchangeDiagram.ProductRow.First

open EtaleGraphPresentation

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (d₁ d₂ : EtaleGraphInterchangeDiagram f g)
  (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The commutative e-side square, without the k-side square.
Source: Stacks Tags 0F7C and 0F7J
(auxiliary; not a blueprint node). -/
lemma e_side_square : CommSq (E d₁ d₂)
    (EtaleGraphPresentation.ProductRow.q
      d₁.compositePresentation d₂.compositePresentation false)
    (qN d₁ d₂) (d d₁ d₂).e := ⟨E_qN d₁ d₂⟩

/-- The two projections of R give the same proper composite.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma R_q : R d₁ d₂ ≫ EtaleGraphPresentation.ProductRow.q
      (ofCompactification d₁.compactification) (ofCompactification d₂.compactification)
      false = qN d₁ d₂ ≫ (d d₁ d₂).r := pullback.lift_snd _ _ _

/-- Transport just the e-side source word to the mixed neighborhood.
It splits the composite graph, exchanges e, and changes the factorization of the
proper composite qN r to R qG. It contains neither the B inverse nor the k exchange.
Source: Stacks Tags 0F7C and 0F7J
(auxiliary; not a blueprint node). -/
def sourceTransport : (d d₁ d₂).sourcePresentation.functor A ≅
    F₀ d₁ d₂ A ⋙ R((EtaleGraphPresentation.ProductRow.q
      (ofCompactification d₁.compactification) (ofCompactification d₂.compactification)
      false)_*[ModuleCat.{u + 1} A]) :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) (H d₁ d₂).a
        (EtaleGraphPresentation.ProductRow.q
          d₁.compositePresentation d₂.compositePresentation false)
        (d d₁ d₂).a (EtaleGraphPresentation.ProductRow.z_q
          d₁.compositePresentation d₂.compositePresentation false)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (etaleGraphNormalizedProperOpenExchange A (E d₁ d₂)
            (EtaleGraphPresentation.ProductRow.q
              d₁.compositePresentation d₂.compositePresentation false)
            (qN d₁ d₂) (d d₁ d₂).e (e_side_square d₁ d₂)) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
            (qN d₁ d₂) (d d₁ d₂).r
            (R d₁ d₂ ≫ EtaleGraphPresentation.ProductRow.q
              (ofCompactification d₁.compactification)
              (ofCompactification d₂.compactification) false) (R_q d₁ d₂).symm ≪≫
            (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (R d₁ d₂)
              (EtaleGraphPresentation.ProductRow.q
                (ofCompactification d₁.compactification)
                (ofCompactification d₂.compactification) false)).symm)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The ambient change for g after splitting off its identity graph.
Source: Stacks Tags 0F7C and 0F7J
(auxiliary; not a blueprint node). -/
def middleTail :
    R((EtaleGraphPresentation.ProductRow.q
        (ofCompactification d₁.compactification) (ofCompactification d₂.compactification)
        false)_*[ModuleCat.{u + 1} A]) ⋙
        (D(((d d₁ d₂).i)_!open[ModuleCat.{u + 1} A]) ⋙
          R(((d d₁ d₂).q)_*[ModuleCat.{u + 1} A])) ≅
      D(((G d₁ d₂).e)_!open[ModuleCat.{u + 1} A]) ⋙
        R(((G d₁ d₂).p)_*[ModuleCat.{u + 1} A]) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A
      (IsPullback.of_hasPullback (prG d₁ d₂) (d d₁ d₂).i).flip) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (prG d₁ d₂) (d d₁ d₂).q (G d₁ d₂).p
        (EtaleGraphPresentation.ProductRow.projection_p
          (ofCompactification d₁.compactification)
          (ofCompactification d₂.compactification) false))

end EtaleGraphInterchangeDiagram.ProductRow.First

namespace EtaleGraphInterchangeDiagram.ProductRow.Second

open EtaleGraphPresentation

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (d₁ d₂ : EtaleGraphInterchangeDiagram f g)
  (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The commutative e-side square, without the k-side square.
Source: Stacks Tags 0F7C and 0F7J
(auxiliary; not a blueprint node). -/
lemma e_side_square : CommSq (E d₁ d₂)
    (EtaleGraphPresentation.ProductRow.q
      d₁.compositePresentation d₂.compositePresentation true)
    (qN d₁ d₂) (d d₁ d₂).e := ⟨E_qN d₁ d₂⟩

/-- The two projections of R give the same proper composite.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
lemma R_q : R d₁ d₂ ≫ EtaleGraphPresentation.ProductRow.q
      (ofCompactification d₁.compactification) (ofCompactification d₂.compactification)
      true = qN d₁ d₂ ≫ (d d₁ d₂).r := pullback.lift_snd _ _ _

/-- Transport just the e-side source word to the mixed neighborhood.
It splits the composite graph, exchanges e, and changes the factorization of the
proper composite qN r to R qG. It contains neither the B inverse nor the k exchange.
Source: Stacks Tags 0F7C and 0F7J
(auxiliary; not a blueprint node). -/
def sourceTransport : (d d₁ d₂).sourcePresentation.functor A ≅
    F₀ d₁ d₂ A ⋙ R((EtaleGraphPresentation.ProductRow.q
      (ofCompactification d₁.compactification) (ofCompactification d₂.compactification)
      true)_*[ModuleCat.{u + 1} A]) :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) (H d₁ d₂).a
        (EtaleGraphPresentation.ProductRow.q
          d₁.compositePresentation d₂.compositePresentation true)
        (d d₁ d₂).a (EtaleGraphPresentation.ProductRow.z_q
          d₁.compositePresentation d₂.compositePresentation true)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (etaleGraphNormalizedProperOpenExchange A (E d₁ d₂)
            (EtaleGraphPresentation.ProductRow.q
              d₁.compositePresentation d₂.compositePresentation true)
            (qN d₁ d₂) (d d₁ d₂).e (e_side_square d₁ d₂)) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
            (qN d₁ d₂) (d d₁ d₂).r
            (R d₁ d₂ ≫ EtaleGraphPresentation.ProductRow.q
              (ofCompactification d₁.compactification)
              (ofCompactification d₂.compactification) true) (R_q d₁ d₂).symm ≪≫
            (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (R d₁ d₂)
              (EtaleGraphPresentation.ProductRow.q
                (ofCompactification d₁.compactification)
                (ofCompactification d₂.compactification) true)).symm)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The ambient change for g after splitting off its identity graph.
Source: Stacks Tags 0F7C and 0F7J
(auxiliary; not a blueprint node). -/
def middleTail :
    R((EtaleGraphPresentation.ProductRow.q
        (ofCompactification d₁.compactification) (ofCompactification d₂.compactification)
        true)_*[ModuleCat.{u + 1} A]) ⋙
        (D(((d d₁ d₂).i)_!open[ModuleCat.{u + 1} A]) ⋙
          R(((d d₁ d₂).q)_*[ModuleCat.{u + 1} A])) ≅
      D(((G d₁ d₂).e)_!open[ModuleCat.{u + 1} A]) ⋙
        R(((G d₁ d₂).p)_*[ModuleCat.{u + 1} A]) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A
      (IsPullback.of_hasPullback (prG d₁ d₂) (d d₁ d₂).i).flip) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (prG d₁ d₂) (d d₁ d₂).q (G d₁ d₂).p
        (EtaleGraphPresentation.ProductRow.projection_p
          (ofCompactification d₁.compactification)
          (ofCompactification d₂.compactification) true))

end EtaleGraphInterchangeDiagram.ProductRow.Second

end AlgebraicGeometry.Etale
