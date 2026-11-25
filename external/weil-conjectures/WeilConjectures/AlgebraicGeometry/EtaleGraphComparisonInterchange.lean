/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphInterchangeData
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductRowPasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSidePasting

/-! # Graph comparisons and proper/open interchange

Source: Stacks Project, Tag 0F7J
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

private theorem cancel_product_boundaries
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F₁ F₂ F₀ : C ⥤ D} {G₁ G₂ G₀ : D ⥤ E} {H₁ H₂ H₀ : C ⥤ E}
    (a₁ : F₁ ≅ F₀) (a₂ : F₂ ≅ F₀) (b₁ : G₁ ≅ G₀) (b₂ : G₂ ≅ G₀)
    (c₁ : H₁ ≅ H₀) (c₂ : H₂ ≅ H₀)
    (I₁ : F₁ ⋙ G₁ ≅ H₁) (I₂ : F₂ ⋙ G₂ ≅ H₂) (U : F₀ ⋙ G₀ ≅ H₀)
    (h₁ : I₁.hom ≫ c₁.hom =
      Functor.whiskerRight a₁.hom G₁ ≫ Functor.whiskerLeft F₀ b₁.hom ≫ U.hom)
    (h₂ : I₂.hom ≫ c₂.hom =
      Functor.whiskerRight a₂.hom G₂ ≫ Functor.whiskerLeft F₀ b₂.hom ≫ U.hom) :
    I₁.hom ≫ (c₁ ≪≫ c₂.symm).hom =
      Functor.whiskerRight (a₁ ≪≫ a₂.symm).hom G₁ ≫
        Functor.whiskerLeft F₂ (b₁ ≪≫ b₂.symm).hom ≫ I₂.hom := by
  apply (cancel_mono c₂.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [h₁, h₂]
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [← b₂.inv.naturality_assoc (a₂.hom.app M),
    ← b₁.hom.naturality_assoc (a₂.hom.app M)]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, Category.comp_id, Iso.inv_hom_id_app_assoc]

private theorem shrink_cancel
    {C : Type*} [Category C] {B O₁ O₂ N₁ N₂ F₁ F₂ : C}
    (a₁ : B ≅ O₁) (a₂ : B ≅ O₂) (m₁ : O₁ ≅ N₁) (m₂ : O₂ ≅ N₂)
    (b₁ : F₁ ≅ N₁) (b₂ : F₂ ≅ N₂) (T : N₁ ≅ N₂) (I : F₁ ≅ F₂)
    (hs : b₁.hom ≫ T.hom = I.hom ≫ b₂.hom)
    (hm : m₁.hom ≫ T.hom = (a₁.symm ≪≫ a₂).hom ≫ m₂.hom) :
    ((a₁ ≪≫ m₁ ≪≫ b₁.symm).symm ≪≫ (a₂ ≪≫ m₂ ≪≫ b₂.symm)).hom = I.hom := by
  apply (cancel_epi (a₁ ≪≫ m₁ ≪≫ b₁.symm).hom).1
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  apply (cancel_mono b₂.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hs]
  simp only [Iso.inv_hom_id_assoc]
  rw [hm]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

private theorem graphComparison_shrink
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z W : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
    (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
    [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a) :
    (etaleGraphComparison A c H (H.shrink a' v fac)).hom =
      (etaleGraphShrinkInterchange A H a' v fac).hom := by
  let S := H.shrink a' v fac
  have hside := etaleGraphShrinkSidePasting A c H a' v fac
  have hmiddle := etaleGraphShrinkMiddlePasting A c H a' v fac
  have hfrom (t : EtaleGraphPresentation h) :
      etaleGraphComparisonFromOpen A c t =
        t.graphSide₁ c A ≪≫ t.graphMiddle c A ≪≫ (t.graphSide₂ c A).symm := by
    apply Iso.ext
    simp only [etaleGraphComparisonFromOpen, locallyClosedGraphIso,
      EtaleGraphPresentation.graphSide₁, EtaleGraphPresentation.graphSide₂,
      EtaleGraphPresentation.graphMiddle, Iso.trans_hom, Category.assoc]
  unfold etaleGraphComparison
  rw [hfrom H, hfrom S]
  exact shrink_cancel (H.graphSide₁ c A) (S.graphSide₁ c A)
    (H.graphMiddle c A) (S.graphMiddle c A) (H.graphSide₂ c A) (S.graphSide₂ c A)
    (H.graphNeighborhoodTriangle c A a' v fac) (etaleGraphShrinkInterchange A H a' v fac)
    hside hmiddle

/-- Product-graph comparisons identify the elementary neighborhood move and intertwine
proper/open interchange for arbitrary two supplied diagrams.

Source: Stacks Project, Tag 0F7J, independence of choices, final A--F comparison;
agent product-graph extension (auxiliary; not a blueprint node).

Proof:
1. For the neighborhood move, fix the auxiliary compactification c. The graph products
and first neighborhoods agree. The second neighborhoods differ by v times the identity;
the intersections differ by its pullback. The proper graph maps compose with these opens
by equality of both projections (locally-closed-graph-model and fibre-product).
2. Expand both B maps as B₂ inverse, proper image of B₁₂, and B₁. The horizontal exchange
law compares the side squares; the vertical law compares the graph triangle stacked above
the side square. Cancel the common side exchange. Naturality moves the graph triangle
past the remaining side exchange. In the intersections the two smaller graph triangles
cancel by the horizontal law. Thus B_S equals the specified inverse triangle word times
B_H. Use proper-open-exchange-cube and extension-zero-composition throughout.
3. The definition C_SH = B_S B_H inverse gives the first assertion. Composite adjunctions
and the open triple-composition identity normalize every cancellation, as in
ringed-derived-monoidal-comparisons.
4. For two diagrams form Y₀ = Y×_Z Y, T₀, P₀, V₀, W₀ as pairwise products over Z,
and V_c, W_c as products over Y. The diagonal Y->Y₀ is closed: it is the pullback of
the closed diagonal of q₁ along i₁×i₁, since i₁ is mono. Hence V_c->V₀ and W_c->W₀
are proper. The graph lifts into W_c and W₀ are proper by proper-to-separated-target.
All supporting opens are products or pullbacks of the supplied opens.
5. Pairwise-product-graph-normalization supplies dν-lambda, tν-lambda, sν-lambda to the
three common graph words, with C_21 = lambda₂ inverse times lambda₁. Let K be the
inverse exchange for the Cartesian square W_c->W₀ over V_c->V₀, under Rr₀. Let I₀
be exchange for the product proper/open square, under Rq₀ and after Je₀ Ra₀.
6. Expand these three lambda maps by their three-arrow formulas. Insert the intermediate
opens Vν×_Z Pother and Pν×_Z Vother. The grid consists of Cartesian side squares,
graph triangles and the supplied squares Qν and Q₀, all with the same normalization.
7. Evaluate the grid by rows and columns. Vertical and horizontal exchange laws compose
its cells. For cells meeting at a vertex use whiskerLeft_comp_whiskerRight. Cancel
opposite graph triangles. The row boundary is sν-lambda Iν; the column boundary is
I₀ (G₀ K) (dν-lambda F_c) F_dν(tν-lambda), with the square for K in inverse direction.
This is equality of derived natural transformations, without a stalkwise inference.
8. Cancel the common I₀(G₀K) for ν = 1,2. Expanding the remaining lambda inverses and
using naturality yields (C_d21 F_t2) F_d1(C_t21). Substituting all three pairwise
normalizations gives the second assertion. No Cartesian hypothesis on Qν, map between
the diagrams, quasi-compactness, Noetherianity, boundedness or constructibility is used. -/
theorem etaleGraphComparisonInterchange (A : Type (u + 1)) [CommRing A] [Finite A] :
    (∀ {X Z W : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
      (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
      [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a),
      (etaleGraphComparison A c H (H.shrink a' v fac)).hom =
        (etaleGraphShrinkInterchange A H a' v fac).hom) ∧
    (∀ {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
      (cf : Compactification f) (ch : Compactification (f ≫ g))
      (d₁ d₂ : EtaleGraphInterchangeDiagram f g),
      (etaleGraphDiagramInterchange A d₁).hom ≫
          (etaleGraphComparison A ch d₁.compositePresentation d₂.compositePresentation).hom =
        Functor.whiskerRight
            (etaleGraphComparison A cf d₁.sourcePresentation d₂.sourcePresentation).hom
            ((EtaleGraphPresentation.ofCompactification d₁.compactification).functor A) ≫
          Functor.whiskerLeft (d₂.sourcePresentation.functor A)
            (etaleGraphComparison A d₁.compactification
              (EtaleGraphPresentation.ofCompactification d₁.compactification)
              (EtaleGraphPresentation.ofCompactification d₂.compactification)).hom ≫
          (etaleGraphDiagramInterchange A d₂).hom) := by
  constructor
  · intro X Z W h c H a' v ha hv fac
    exact graphComparison_shrink A c H a' v fac
  · intro X Y Z f g cf ch d₁ d₂
    have hf := etalePairwiseProductGraphNormalization A cf
      d₁.sourcePresentation d₂.sourcePresentation
    have hg := etalePairwiseProductGraphNormalization A d₁.compactification
      (EtaleGraphPresentation.ofCompactification d₁.compactification)
      (EtaleGraphPresentation.ofCompactification d₂.compactification)
    have hh := etalePairwiseProductGraphNormalization A ch
      d₁.compositePresentation d₂.compositePresentation
    rw [hf, hg, hh]
    exact cancel_product_boundaries
      (d₁.productSourceLambda d₂ A false) (d₁.productSourceLambda d₂ A true)
      (d₁.productMiddleLambda d₂ A false) (d₁.productMiddleLambda d₂ A true)
      (d₁.productCompositeLambda d₂ A false) (d₁.productCompositeLambda d₂ A true)
      (etaleGraphDiagramInterchange A d₁) (etaleGraphDiagramInterchange A d₂)
      (d₁.productInterchange d₂ A)
      (etaleGraphProductRowPasting A d₁ d₂ false)
      (etaleGraphProductRowPasting A d₁ d₂ true)

end AlgebraicGeometry.Etale
