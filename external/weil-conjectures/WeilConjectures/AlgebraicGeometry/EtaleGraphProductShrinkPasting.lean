/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientPasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkLift
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkSquare

/-! # Shrinking the three supports in the product interchange grid

Source: Stacks Project, Tag 0F7J, cancellation of the graph triangles in A--F;
the product-graph extension in lem-pur-etale-graph-product-row-pasting.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

/-- Shrinking the three supporting neighborhoods commutes with the fixed product boundary.
The source and target are the already enlarged proper ambient products: this assertion
contains neither the original supplied square exchange nor a proper-ambient lambda.
Source: Stacks Tags 0F7C, 0F7D and the final A--F calculation in 0F7J
(auxiliary; not a blueprint node).

Proof: write n for the selected index and m for the other. The three open inclusions
are W_1 times_Y W_2 into W_n times_Y V_m, Y times_Z Y into Y times_Z T_m,
and W_1 times_Z W_2 into W_n times_Z P_m. The two maps imposing equality over Y
are productBV and productBW. Paste their B square with the square involving the
selected mixed neighborhood V_n times_Z P_m, and paste the product Q square with
its open inclusion into the ambient Q square. The resulting outer squares agree
by their projections. Apply horizontal pasting of normalized proper/open exchanges
to the open edges and vertical pasting to the proper edges. The three identity-top
graph squares compare the proper lifts z_f,z_g,z_h with the product graph lifts.
Their exchange is exactly the inverse triangle factor of shrinkLambda, by Cartesian
normalization and removal of extension by the identity. Naturality interchanges the
factors meeting at a vertex. The two interior graph triangles then cancel; what
remains is the inverse product B exchange followed by the product Q exchange.
The open triple compositor law and proper compositor associativity give the displayed
parenthesizations and identify this boundary with productInterchange. All graph edges
are proper by proper-to-separated. This calculation uses no original square exchange,
no choice of compactification, and no equality inferred from stalks; it applies also
to empty supporting neighborhoods and identity open immersions. -/
theorem etaleGraphProductShrinkPasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (second : Bool) :
    (match second with
    | false =>
      let sf := EtaleGraphPresentation.ProductRow.shrinkLambda
        d₁.sourcePresentation d₂.sourcePresentation false A
      let sg := EtaleGraphPresentation.ProductRow.shrinkLambda
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) false A
      let sh := EtaleGraphPresentation.ProductRow.shrinkLambda
        d₁.compositePresentation d₂.compositePresentation false A
      (EtaleGraphInterchangeDiagram.ProductRow.First.interchange d₁ d₂ A).hom ≫ sh.hom =
        Functor.whiskerRight sf.hom
            ((EtaleGraphInterchangeDiagram.ProductRow.First.G d₁ d₂).functor A) ≫
          Functor.whiskerLeft ((d₁.productF d₂).functor A) sg.hom ≫
          (d₁.productInterchange d₂ A).hom
    | true =>
      let sf := EtaleGraphPresentation.ProductRow.shrinkLambda
        d₁.sourcePresentation d₂.sourcePresentation true A
      let sg := EtaleGraphPresentation.ProductRow.shrinkLambda
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) true A
      let sh := EtaleGraphPresentation.ProductRow.shrinkLambda
        d₁.compositePresentation d₂.compositePresentation true A
      (EtaleGraphInterchangeDiagram.ProductRow.Second.interchange d₁ d₂ A).hom ≫ sh.hom =
        Functor.whiskerRight sf.hom
            ((EtaleGraphInterchangeDiagram.ProductRow.Second.G d₁ d₂).functor A) ≫
          Functor.whiskerLeft ((d₁.productF d₂).functor A) sg.hom ≫
          (d₁.productInterchange d₂ A).hom
    ) := by
  have h (b : Bool) :
      (EtaleGraphInterchangeDiagram.ProductShrink.liftBoundary d₁ d₂ b A).hom ≫
          (EtaleGraphInterchangeDiagram.ProductShrink.squareInterchange d₁ d₂ b A).hom ≫
          (EtaleGraphInterchangeDiagram.ProductShrink.compositeShrink d₁ d₂ b A).hom =
        (EtaleGraphInterchangeDiagram.ProductShrink.inputBoundary d₁ d₂ b A).hom ≫
          (EtaleGraphInterchangeDiagram.ProductShrink.productLiftBoundary d₁ d₂ A).hom ≫
          (d₁.productSquareInterchange d₂ A).hom := by
    rw [etaleGraphProductShrinkSquare A d₁ d₂ b, ← Category.assoc,
      etaleGraphProductShrinkLift A d₁ d₂ b, Category.assoc]
  cases second
  · simpa only [EtaleGraphInterchangeDiagram.ProductShrink.liftBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.liftInterchange,
      EtaleGraphInterchangeDiagram.ProductShrink.squareInterchange,
      EtaleGraphInterchangeDiagram.ProductShrink.inputBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.productLiftBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.sourceShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.middleShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.compositeShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.F,
      EtaleGraphInterchangeDiagram.ProductShrink.G,
      EtaleGraphInterchangeDiagram.ProductShrink.H,
      EtaleGraphInterchangeDiagram.ProductRow.First.F,
      EtaleGraphInterchangeDiagram.ProductRow.First.G,
      EtaleGraphInterchangeDiagram.ProductRow.First.H,
      EtaleGraphInterchangeDiagram.ProductRow.Second.F,
      EtaleGraphInterchangeDiagram.ProductRow.Second.G,
      EtaleGraphInterchangeDiagram.ProductRow.Second.H,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      EtaleGraphInterchangeDiagram.ProductRow.First.interchange,
      EtaleGraphInterchangeDiagram.productInterchange, Iso.trans_hom, Category.assoc]
      using h false
  · simpa only [EtaleGraphInterchangeDiagram.ProductShrink.liftBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.liftInterchange,
      EtaleGraphInterchangeDiagram.ProductShrink.squareInterchange,
      EtaleGraphInterchangeDiagram.ProductShrink.inputBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.productLiftBoundary,
      EtaleGraphInterchangeDiagram.ProductShrink.sourceShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.middleShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.compositeShrink,
      EtaleGraphInterchangeDiagram.ProductShrink.F,
      EtaleGraphInterchangeDiagram.ProductShrink.G,
      EtaleGraphInterchangeDiagram.ProductShrink.H,
      EtaleGraphInterchangeDiagram.ProductRow.First.F,
      EtaleGraphInterchangeDiagram.ProductRow.First.G,
      EtaleGraphInterchangeDiagram.ProductRow.First.H,
      EtaleGraphInterchangeDiagram.ProductRow.Second.F,
      EtaleGraphInterchangeDiagram.ProductRow.Second.G,
      EtaleGraphInterchangeDiagram.ProductRow.Second.H,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      EtaleGraphInterchangeDiagram.ProductRow.Second.interchange,
      EtaleGraphInterchangeDiagram.productInterchange, Iso.trans_hom, Category.assoc]
      using h true

end AlgebraicGeometry.Etale
