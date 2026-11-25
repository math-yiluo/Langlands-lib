/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientPasting

/-! # The mixed-neighborhood boundary in the product shrink grid

Source: Stacks Project, Tags 0F7C, 0F7D and the A--F calculation of Tag 0F7J.
(auxiliary; not a blueprint node).

The middle boundary is constructed from the composite graph triangle, open
compositors, and the inverse exchange for the mixed-neighborhood inclusion.
It does not use either the lift interchange or the final square interchange.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.EtaleGraphInterchangeDiagram.ProductShrink

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (second : Bool)

/-- The selected source neighborhood presentation.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev F := EtaleGraphPresentation.ProductRow.ambient
  d₁.sourcePresentation d₂.sourcePresentation second
/-- The selected middle neighborhood presentation.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev G := EtaleGraphPresentation.ProductRow.ambient
  (EtaleGraphPresentation.ofCompactification d₁.compactification)
  (EtaleGraphPresentation.ofCompactification d₂.compactification) second
/-- The selected composite neighborhood presentation.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev H := EtaleGraphPresentation.ProductRow.ambient
  d₁.compositePresentation d₂.compositePresentation second

/-- The inclusion of the source product support.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev vf := EtaleGraphPresentation.ProductRow.v
  d₁.sourcePresentation d₂.sourcePresentation second
/-- The inclusion of the middle product support.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev vg := EtaleGraphPresentation.ProductRow.v
  (EtaleGraphPresentation.ofCompactification d₁.compactification)
  (EtaleGraphPresentation.ofCompactification d₂.compactification) second
/-- The inclusion of the composite product support.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev vh := EtaleGraphPresentation.ProductRow.v
  d₁.compositePresentation d₂.compositePresentation second

/-- The selected mixed neighborhood in the composite ambient product.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev N : Scheme.{u} := match second with
  | false => ProductRow.First.N d₁ d₂
  | true => ProductRow.Second.N d₁ d₂

/-- The open inclusion of the composite neighborhood into the mixed neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def E : (H d₁ d₂ second).U ⟶ N d₁ d₂ second := by
  cases second
  · exact ProductRow.First.E d₁ d₂
  · exact ProductRow.Second.E d₁ d₂

/-- The open inclusion of the mixed neighborhood into the ambient product.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def K : N d₁ d₂ second ⟶ (d₁.productH d₂).P := by
  cases second
  · exact ProductRow.First.K d₁ d₂
  · exact ProductRow.Second.K d₁ d₂

/-- The proper map from the mixed neighborhood to the middle neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def R : N d₁ d₂ second ⟶ (G d₁ d₂ second).U := by
  cases second
  · exact ProductRow.First.R d₁ d₂
  · exact ProductRow.Second.R d₁ d₂

/-- The selected proper inclusion of the product over Y in the mixed neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def BV : (d₁.productF d₂).P ⟶ N d₁ d₂ second := by
  cases second
  · exact ProductRow.First.BV d₁ d₂
  · exact ProductRow.Second.BV d₁ d₂

/-- The selected proper map between the source and composite neighborhoods.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def BW : (F d₁ d₂ second).U ⟶ (H d₁ d₂ second).U := by
  cases second
  · exact ProductRow.First.BW d₁ d₂
  · exact ProductRow.Second.BW d₁ d₂

/-- The selected B proper edge is proper.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
instance BV_proper : IsProper (BV d₁ d₂ second) := by
  cases second <;> dsimp only [BV] <;> infer_instance

/-- The selected B graph edge is proper.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
instance BW_proper : IsProper (BW d₁ d₂ second) := by
  cases second <;> dsimp only [BW] <;> infer_instance

/-- The ambient projection of the selected proper B edge.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma BV_K : BV d₁ d₂ second ≫ K d₁ d₂ second =
    d₁.productBV d₂ ≫ d₁.productK d₂ := by
  cases second <;> exact pullback.lift_fst _ _ _

/-- The source-to-composite neighborhood map respects the ambient opens.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma BW_e : BW d₁ d₂ second ≫ (H d₁ d₂ second).e =
    (F d₁ d₂ second).e ≫ d₁.productBV d₂ ≫ d₁.productK d₂ := by
  cases second
  · exact ProductRow.First.BW_e d₁ d₂
  · exact ProductRow.Second.BW_e d₁ d₂

/-- The selected composite-neighborhood inclusion is open.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
instance E_open : IsOpenImmersion (E d₁ d₂ second) := by
  cases second <;> dsimp only [E] <;> infer_instance
/-- The selected mixed-neighborhood inclusion is open.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
instance K_open : IsOpenImmersion (K d₁ d₂ second) := by
  cases second <;> dsimp only [K] <;> infer_instance
/-- The selected mixed-neighborhood projection is proper.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
instance R_proper : IsProper (R d₁ d₂ second) := by
  cases second <;> dsimp only [R] <;> infer_instance

/-- The composite of the two ambient open inclusions is the composite support open.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma E_K : E d₁ d₂ second ≫ K d₁ d₂ second = (H d₁ d₂ second).e := by
  cases second
  · exact ProductRow.First.E_K d₁ d₂
  · exact ProductRow.Second.E_K d₁ d₂

/-- The selected mixed-neighborhood Q square commutes.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma R_e : R d₁ d₂ second ≫ (G d₁ d₂ second).e =
    K d₁ d₂ second ≫ d₁.productP d₂ := by
  cases second
  · exact (ProductRow.First.Q_square d₁ d₂).w.symm
  · exact (ProductRow.Second.Q_square d₁ d₂).w.symm

/-- Include the product of both V opens in the selected mixed neighborhood.
Source: Stacks Tag 0F7J, intermediate square F in the product extension.
(auxiliary; not a blueprint node). -/
def n : d₁.productV d₂ ⟶ N d₁ d₂ second := by
  cases second
  · exact pullback.lift (d₁.productK d₂) (pullback.fst _ _) (by
      change d₁.productK d₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d₁.k
      simp only [productK, pullback.map, pullback.lift_fst])
  · exact pullback.lift (d₁.productK d₂) (pullback.snd _ _) (by
      change d₁.productK d₂ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ d₂.k
      simp only [productK, pullback.map, pullback.lift_snd])

/-- The mixed-neighborhood inclusion factors the product open.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma n_K : n d₁ d₂ second ≫ K d₁ d₂ second = d₁.productK d₂ := by
  cases second <;> exact pullback.lift_fst _ _ _

/-- The product-to-mixed-neighborhood map is open by cancellation.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
instance n_open : IsOpenImmersion (n d₁ d₂ second) := by
  have : IsOpenImmersion (n d₁ d₂ second ≫ K d₁ d₂ second) := by
    rw [n_K]
    infer_instance
  exact IsOpenImmersion.of_comp _ (K d₁ d₂ second)

/-- The two paths of open inclusions out of the composite product support agree.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma vh_E : vh d₁ d₂ second ≫ E d₁ d₂ second =
    d₁.productE d₂ ≫ n d₁ d₂ second := by
  apply (cancel_mono (K d₁ d₂ second)).1
  simp only [Category.assoc, E_K, n_K]
  exact (EtaleGraphPresentation.ProductRow.v_j
    d₁.compositePresentation d₂.compositePresentation second).trans
      (d₁.productE_productK d₂).symm

/-- The mixed-neighborhood shrink square commutes.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma n_R : n d₁ d₂ second ≫ R d₁ d₂ second =
    d₁.productR d₂ ≫ vg d₁ d₂ second := by
  apply (cancel_mono ((G d₁ d₂ second).e)).1
  calc
    (n d₁ d₂ second ≫ R d₁ d₂ second) ≫ (G d₁ d₂ second).e =
        n d₁ d₂ second ≫ (R d₁ d₂ second ≫ (G d₁ d₂ second).e) :=
      Category.assoc _ _ _
    _ = n d₁ d₂ second ≫ (K d₁ d₂ second ≫ d₁.productP d₂) :=
      congrArg (n d₁ d₂ second ≫ ·) (R_e d₁ d₂ second)
    _ = d₁.productK d₂ ≫ d₁.productP d₂ := by rw [← Category.assoc, n_K]
    _ = d₁.productR d₂ ≫ (d₁.productG d₂).e := (d₁.product_square d₂).w
    _ = d₁.productR d₂ ≫ (vg d₁ d₂ second ≫ (G d₁ d₂ second).e) :=
      congrArg (d₁.productR d₂ ≫ ·)
        (EtaleGraphPresentation.ProductRow.v_j
          (EtaleGraphPresentation.ofCompactification d₁.compactification)
          (EtaleGraphPresentation.ofCompactification d₂.compactification) second).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The proper B edge factors through the smaller mixed neighborhood.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma productBV_n : d₁.productBV d₂ ≫ n d₁ d₂ second = BV d₁ d₂ second := by
  apply (cancel_mono (K d₁ d₂ second)).1
  rw [Category.assoc, n_K, BV_K]

/-- The source and composite support inclusions commute with the B graph edges.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma vf_BW : vf d₁ d₂ second ≫ BW d₁ d₂ second =
    d₁.productBW d₂ ≫ vh d₁ d₂ second := by
  apply (cancel_mono ((H d₁ d₂ second).e)).1
  calc
    (vf d₁ d₂ second ≫ BW d₁ d₂ second) ≫ (H d₁ d₂ second).e =
        vf d₁ d₂ second ≫ (BW d₁ d₂ second ≫ (H d₁ d₂ second).e) :=
      Category.assoc _ _ _
    _ = vf d₁ d₂ second ≫
        ((F d₁ d₂ second).e ≫ d₁.productBV d₂ ≫ d₁.productK d₂) :=
      congrArg (vf d₁ d₂ second ≫ ·) (BW_e d₁ d₂ second)
    _ = (d₁.productF d₂).e ≫ d₁.productBV d₂ ≫ d₁.productK d₂ := by
      rw [← Category.assoc, EtaleGraphPresentation.ProductRow.v_j]
    _ = (d₁.productBW d₂ ≫ d₁.productE d₂) ≫ d₁.productK d₂ := by
      rw [← Category.assoc, (d₁.productB_square d₂).w]
    _ = d₁.productBW d₂ ≫ (d₁.productH d₂).e := by
      rw [Category.assoc, d₁.productE_productK d₂]
    _ = d₁.productBW d₂ ≫ (vh d₁ d₂ second ≫ (H d₁ d₂ second).e) :=
      congrArg (d₁.productBW d₂ ≫ ·)
        (EtaleGraphPresentation.ProductRow.v_j
          d₁.compositePresentation d₂.compositePresentation second).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The commutative square used for the middle boundary exchange.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
lemma shrink_square : CommSq (n d₁ d₂ second) (d₁.productR d₂)
    (R d₁ d₂ second) (vg d₁ d₂ second) := ⟨n_R d₁ d₂ second⟩

/-- The final open and proper factors of the ambient middle presentation.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev suffix (A : Type (u + 1)) [CommRing A] :=
  D(((G d₁ d₂ second).e)_!open[ModuleCat.{u + 1} A]) ⋙
    R(((G d₁ d₂ second).p)_*[ModuleCat.{u + 1} A])
/-- The final open and proper factors of the product middle presentation.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev productSuffix (A : Type (u + 1)) [CommRing A] :=
  D(((d₁.productG d₂).e)_!open[ModuleCat.{u + 1} A]) ⋙
    R(((d₁.productG d₂).p)_*[ModuleCat.{u + 1} A])
/-- The selected mixed word before its final open and proper factors.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
abbrev F₀ (A : Type (u + 1)) [CommRing A] :=
  R(((H d₁ d₂ second).a)_*[ModuleCat.{u + 1} A]) ⋙
    D((E d₁ d₂ second)_!open[ModuleCat.{u + 1} A]) ⋙
      R((R d₁ d₂ second)_*[ModuleCat.{u + 1} A])

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The selected inverse B exchange, with its proper compositors.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def liftInterchange :
    (F d₁ d₂ second).functor A ⋙
        R(((G d₁ d₂ second).a)_*[ModuleCat.{u + 1} A]) ≅ F₀ d₁ d₂ second A := by
  cases second
  · exact ProductRow.First.liftInterchange d₁ d₂ A
  · exact ProductRow.Second.liftInterchange d₁ d₂ A

/-- The selected Q exchange, with its open and proper compositors.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def squareInterchange : F₀ d₁ d₂ second A ⋙ suffix d₁ d₂ second A ≅
    (H d₁ d₂ second).functor A := by
  cases second
  · exact ProductRow.First.squareInterchange d₁ d₂ A
  · exact ProductRow.Second.squareInterchange d₁ d₂ A

/-- The boundary ending after the inverse B exchange, before the Q exchange. -/
def liftBoundary : (F d₁ d₂ second).functor A ⋙ (G d₁ d₂ second).functor A ≅
    F₀ d₁ d₂ second A ⋙ suffix d₁ d₂ second A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (liftInterchange d₁ d₂ second A) _

/-- The corresponding boundary for the product supports. -/
def productLiftBoundary : (d₁.productF d₂).functor A ⋙ (d₁.productG d₂).functor A ≅
    d₁.productF₀ d₂ A ⋙ productSuffix d₁ d₂ A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (d₁.productLiftInterchange d₂ A) _

/-- Open composition across the upper rectangle of the mixed-neighborhood square. -/
def openRectangle :
    D((vh d₁ d₂ second)_!open[ModuleCat.{u + 1} A]) ⋙
        D((E d₁ d₂ second)_!open[ModuleCat.{u + 1} A]) ≅
      D((d₁.productE d₂)_!open[ModuleCat.{u + 1} A]) ⋙
        D((n d₁ d₂ second)_!open[ModuleCat.{u + 1} A]) :=
  (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
    (vh d₁ d₂ second) (E d₁ d₂ second)).symm ≪≫
  mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
    (vh_E d₁ d₂ second) ≪≫
  mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
    (d₁.productE d₂) (n d₁ d₂ second)

/-- Change the mixed word by the graph triangle and the inverse mixed square.
This definition uses neither of the B or Q interchanges.
Source: Stacks Tags 0F7C, 0F7D and 0F7J.
(auxiliary; not a blueprint node). -/
def middle : F₀ d₁ d₂ second A ≅
    d₁.productF₀ d₂ A ⋙ D((vg d₁ d₂ second)_!open[ModuleCat.{u + 1} A]) :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
        (d₁.productH d₂).a (vh d₁ d₂ second) (H d₁ d₂ second).a rfl).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (openRectangle d₁ d₂ second A) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (etaleGraphNormalizedProperOpenExchange A (n d₁ d₂ second)
            (d₁.productR d₂) (R d₁ d₂ second) (vg d₁ d₂ second)
            (shrink_square d₁ d₂ second)).symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Extend the explicit mixed word by the common final open and proper factors. -/
def middleBoundary : F₀ d₁ d₂ second A ⋙ suffix d₁ d₂ second A ≅
    d₁.productF₀ d₂ A ⋙ productSuffix d₁ d₂ A :=
  Functor.isoWhiskerRight (middle d₁ d₂ second A) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
              (vg d₁ d₂ second) (G d₁ d₂ second).e).symm ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
              (EtaleGraphPresentation.ProductRow.v_j
                (EtaleGraphPresentation.ofCompactification d₁.compactification)
                (EtaleGraphPresentation.ofCompactification d₂.compactification) second)) _)

/-- The source support shrink map of the supplied product row. -/
abbrev sourceShrink := EtaleGraphPresentation.ProductRow.shrinkLambda
  d₁.sourcePresentation d₂.sourcePresentation second A
/-- The middle support shrink map of the supplied product row. -/
abbrev middleShrink := EtaleGraphPresentation.ProductRow.shrinkLambda
  (EtaleGraphPresentation.ofCompactification d₁.compactification)
  (EtaleGraphPresentation.ofCompactification d₂.compactification) second A
/-- The composite support shrink map of the supplied product row. -/
abbrev compositeShrink := EtaleGraphPresentation.ProductRow.shrinkLambda
  d₁.compositePresentation d₂.compositePresentation second A

/-- Shrink the input supports, in the order fixed by the statement. -/
def inputBoundary : (F d₁ d₂ second).functor A ⋙ (G d₁ d₂ second).functor A ≅
    (d₁.productF d₂).functor A ⋙ (d₁.productG d₂).functor A :=
  Functor.isoWhiskerRight (sourceShrink d₁ d₂ second A) _ ≪≫
    Functor.isoWhiskerLeft _ (middleShrink d₁ d₂ second A)

end AlgebraicGeometry.Etale.EtaleGraphInterchangeDiagram.ProductShrink
