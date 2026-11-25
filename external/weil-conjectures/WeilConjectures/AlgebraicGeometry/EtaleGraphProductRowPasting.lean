/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProductInterchange
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkPasting

/-! # One row of the graph product interchange grid

Source: Stacks Project, Tag 0F7J, A--F pasting in the product neighborhoods
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

namespace EtaleGraphInterchangeDiagram

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (d₁ d₂ : EtaleGraphInterchangeDiagram f g)
  (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The source lambda for a selected side of the common product diagram.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def productSourceLambda (second : Bool) :
    (if second then d₂ else d₁).sourcePresentation.functor A ≅
      (d₁.productF d₂).functor A := by
  cases second
  · exact EtaleGraphPresentation.PairwiseProduct.lambda₁
      d₁.sourcePresentation d₂.sourcePresentation A
  · exact EtaleGraphPresentation.PairwiseProduct.lambda₂
      d₁.sourcePresentation d₂.sourcePresentation A

/-- The middle lambda for a selected side of the common product diagram.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def productMiddleLambda (second : Bool) :
    (EtaleGraphPresentation.ofCompactification
      (if second then d₂ else d₁).compactification).functor A ≅
      (d₁.productG d₂).functor A := by
  cases second
  · exact EtaleGraphPresentation.PairwiseProduct.lambda₁
      (EtaleGraphPresentation.ofCompactification d₁.compactification)
      (EtaleGraphPresentation.ofCompactification d₂.compactification) A
  · exact EtaleGraphPresentation.PairwiseProduct.lambda₂
      (EtaleGraphPresentation.ofCompactification d₁.compactification)
      (EtaleGraphPresentation.ofCompactification d₂.compactification) A

/-- The composite lambda for a selected side of the common product diagram.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def productCompositeLambda (second : Bool) :
    (if second then d₂ else d₁).compositePresentation.functor A ≅
      (d₁.productH d₂).functor A := by
  cases second
  · exact EtaleGraphPresentation.PairwiseProduct.lambda₁
      d₁.compositePresentation d₂.compositePresentation A
  · exact EtaleGraphPresentation.PairwiseProduct.lambda₂
      d₁.compositePresentation d₂.compositePresentation A

end EtaleGraphInterchangeDiagram

/-- A selected side of the product grid evaluates to the fixed common boundary.
This assertion contains no comparison between the two supplied interchange maps and no
auxiliary compactification. Its boundary is defined from the product proper/open square
and the inverse exchange for the closed inclusion of products over Y into products over Z.

Source: Stacks Tag 0F7J, A--F pasting; product-graph extension, steps 6--7 of
lem-pur-etale-graph-comparison-interchange
(auxiliary; not a blueprint node).

Proof: expand the three lambda words, with their two side squares and graph triangles.
For the g word the neighborhoods are Y times T_other and T_selected times Y over Z;
for h they are W_selected times P_other and P_selected times W_other over Z.
For f use W_selected times V_other and V_selected times W_other over Y. Insert
V_selected times P_other and P_selected times V_other over Z. The maps from the
Y-products to the Z-products are productBV and productBW. They are proper because
Y to Y times Y over Z is closed: g is separated, since it is open then proper.
Their square with the products of e is Cartesian, by the pullback universal property.
All side squares are Cartesian base changes of the supplied opens, and all graph
triangles have proper graph edges by proper-to-separated. Evaluate this grid by rows
and by columns. Horizontal pasting combines consecutive open edges; vertical pasting
combines consecutive proper edges. Naturality interchanges cells meeting at a vertex.
Opposite intersection graph triangles cancel. The row boundary is the selected I
followed by its composite lambda. The column boundary is the source lambda, the middle
lambda, the inverse B exchange and Q₀ exchange, including their proper and open
compositors. These last two factors are exactly productInterchange. Cartesian exchange
normalization, the open triple-composition law and composite-adjunction normalization
identify the words, including their associators. No comparison between the two selected
sides is assumed, and no equality is inferred from stalks. -/
theorem etaleGraphProductRowPasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (second : Bool) :
    (etaleGraphDiagramInterchange A (if second then d₂ else d₁)).hom ≫
        (d₁.productCompositeLambda d₂ A second).hom =
      Functor.whiskerRight (d₁.productSourceLambda d₂ A second).hom
          ((EtaleGraphPresentation.ofCompactification
            (if second then d₂ else d₁).compactification).functor A) ≫
        Functor.whiskerLeft ((d₁.productF d₂).functor A)
          (d₁.productMiddleLambda d₂ A second).hom ≫
        (d₁.productInterchange d₂ A).hom := by
  cases second
  · let af := EtaleGraphPresentation.ProductRow.ambientLambda
      d₁.sourcePresentation d₂.sourcePresentation false A
    let ag := EtaleGraphPresentation.ProductRow.ambientLambda
      (EtaleGraphPresentation.ofCompactification d₁.compactification)
      (EtaleGraphPresentation.ofCompactification d₂.compactification) false A
    let ah := EtaleGraphPresentation.ProductRow.ambientLambda
      d₁.compositePresentation d₂.compositePresentation false A
    let sf := EtaleGraphPresentation.ProductRow.shrinkLambda
      d₁.sourcePresentation d₂.sourcePresentation false A
    let sg := EtaleGraphPresentation.ProductRow.shrinkLambda
      (EtaleGraphPresentation.ofCompactification d₁.compactification)
      (EtaleGraphPresentation.ofCompactification d₂.compactification) false A
    let sh := EtaleGraphPresentation.ProductRow.shrinkLambda
      d₁.compositePresentation d₂.compositePresentation false A
    have hf : d₁.productSourceLambda d₂ A false = af ≪≫ sf := by
      exact EtaleGraphPresentation.ProductRow.lambda_factor
        d₁.sourcePresentation d₂.sourcePresentation false A
    have hg : d₁.productMiddleLambda d₂ A false = ag ≪≫ sg := by
      exact EtaleGraphPresentation.ProductRow.lambda_factor
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) false A
    have hh : d₁.productCompositeLambda d₂ A false = ah ≪≫ sh := by
      exact EtaleGraphPresentation.ProductRow.lambda_factor
        d₁.compositePresentation d₂.compositePresentation false A
    rw [hf, hg, hh]
    have ha := etaleGraphProductAmbientPasting A d₁ d₂ false
    have hs := etaleGraphProductShrinkPasting A d₁ d₂ false
    change (etaleGraphDiagramInterchange A (if false then d₂ else d₁)).hom ≫ ah.hom = _
      at ha
    change (EtaleGraphInterchangeDiagram.ProductRow.First.interchange d₁ d₂ A).hom ≫
      sh.hom = _ at hs
    simp only [Iso.trans_hom, Functor.whiskerRight_comp, Functor.whiskerLeft_comp]
    rw [← Category.assoc, ha]
    simp only [Category.assoc]
    rw [hs, Functor.whiskerLeft_comp_whiskerRight_assoc]
    rfl
  · let af := EtaleGraphPresentation.ProductRow.ambientLambda
      d₁.sourcePresentation d₂.sourcePresentation true A
    let ag := EtaleGraphPresentation.ProductRow.ambientLambda
      (EtaleGraphPresentation.ofCompactification d₁.compactification)
      (EtaleGraphPresentation.ofCompactification d₂.compactification) true A
    let ah := EtaleGraphPresentation.ProductRow.ambientLambda
      d₁.compositePresentation d₂.compositePresentation true A
    let sf := EtaleGraphPresentation.ProductRow.shrinkLambda
      d₁.sourcePresentation d₂.sourcePresentation true A
    let sg := EtaleGraphPresentation.ProductRow.shrinkLambda
      (EtaleGraphPresentation.ofCompactification d₁.compactification)
      (EtaleGraphPresentation.ofCompactification d₂.compactification) true A
    let sh := EtaleGraphPresentation.ProductRow.shrinkLambda
      d₁.compositePresentation d₂.compositePresentation true A
    have hf : d₁.productSourceLambda d₂ A true = af ≪≫ sf := by
      exact EtaleGraphPresentation.ProductRow.lambda_factor
        d₁.sourcePresentation d₂.sourcePresentation true A
    have hg : d₁.productMiddleLambda d₂ A true = ag ≪≫ sg := by
      exact EtaleGraphPresentation.ProductRow.lambda_factor
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) true A
    have hh : d₁.productCompositeLambda d₂ A true = ah ≪≫ sh := by
      exact EtaleGraphPresentation.ProductRow.lambda_factor
        d₁.compositePresentation d₂.compositePresentation true A
    rw [hf, hg, hh]
    have ha := etaleGraphProductAmbientPasting A d₁ d₂ true
    have hs := etaleGraphProductShrinkPasting A d₁ d₂ true
    change (etaleGraphDiagramInterchange A (if true then d₂ else d₁)).hom ≫ ah.hom = _
      at ha
    change (EtaleGraphInterchangeDiagram.ProductRow.Second.interchange d₁ d₂ A).hom ≫
      sh.hom = _ at hs
    simp only [Iso.trans_hom, Functor.whiskerRight_comp, Functor.whiskerLeft_comp]
    rw [← Category.assoc, ha]
    simp only [Category.assoc]
    rw [hs, Functor.whiskerLeft_comp_whiskerRight_assoc]
    rfl

end AlgebraicGeometry.Etale
