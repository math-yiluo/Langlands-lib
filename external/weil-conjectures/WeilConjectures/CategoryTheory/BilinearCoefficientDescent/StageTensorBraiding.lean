/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

/-! # Braiding representatives in a directed tensor family

Source: the agent-written common-stage representative construction.
The derived-tensor application follows Stacks 06YS, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u v
open CategoryTheory

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.BilinearCoefficientDescent.output
namespace CategoryTheory.BilinearCoefficientDescent

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  (S : StageSystem C) (U : Family S S S)
  (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)

omit [IsDirectedOrder I] in
private theorem endpoint_tower (X Y : S.PairCategory) {L H : I}
    (h : join X.stage Y.stage ≤ L) (k : L ≤ H) :
    (S.assoc h k).hom.app (output U join left right (X, Y)).obj ≫
        (endpoint U join left right (X, Y) (h.trans k)).hom =
      (S.T k).map (endpoint U join left right (X, Y) h).hom ≫
        (U.comparison k).hom.app (X.toStage ((left _ _).trans h),
          Y.toStage ((right _ _).trans h)) ≫
        (U.U H).map (Prod.mkHom
          ((S.assoc ((left _ _).trans h) k).hom.app X.obj)
          ((S.assoc ((right _ _).trans h) k).hom.app Y.obj)) := by
  dsimp only [endpoint, output, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
    Iso.app_hom]
  rw [Functor.map_comp]
  simp only [Iso.prod_hom, Iso.app_hom, Category.assoc]
  have hn := (U.comparison k).hom.naturality
    (Prod.mkHom ((S.assoc (left X.stage Y.stage) h).hom.app X.obj)
      ((S.assoc (right X.stage Y.stage) h).hom.app Y.obj))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp]
  have he :
      Prod.mkHom ((S.T k).map ((S.assoc (left X.stage Y.stage) h).hom.app X.obj))
        ((S.T k).map ((S.assoc (right X.stage Y.stage) h).hom.app Y.obj)) ≫
        Prod.mkHom ((S.assoc ((left X.stage Y.stage).trans h) k).hom.app X.obj)
          ((S.assoc ((right X.stage Y.stage).trans h) k).hom.app Y.obj) =
      Prod.mkHom ((S.assoc h k).hom.app (X.toStage (left _ _)))
        ((S.assoc h k).hom.app (Y.toStage (right _ _))) ≫
        Prod.mkHom ((S.assoc (left X.stage Y.stage) (h.trans k)).hom.app X.obj)
          ((S.assoc (right X.stage Y.stage) (h.trans k)).hom.app Y.obj) := by
    exact Prod.ext (S.cocycle _ _ _ _) (S.cocycle _ _ _ _)
  rw [he, Functor.map_comp]
  simp only [← Category.assoc]
  have ht := U.tower h k (X.toStage (left _ _)) (Y.toStage (right _ _))
  simp only [← Category.assoc] at ht
  rw [ht]

end CategoryTheory.BilinearCoefficientDescent

namespace CategoryTheory.BilinearCoefficientDescent
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  (S : StageSystem C) (U : Family S S S)
  (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
  (β : ∀ i (X Y : C i), (U.U i).obj (X, Y) ≅ (U.U i).obj (Y, X))
  (hn : ∀ i {X X' Y Y' : C i} (f : X ⟶ X') (g : Y ⟶ Y'),
    (U.U i).map (Prod.mkHom f g) ≫ (β i X' Y').hom =
      (β i X Y).hom ≫ (U.U i).map (Prod.mkHom g f))
  (hc : ∀ {i j : I} (h : i ≤ j) (X Y : C i),
    (S.T h).map (β i X Y).hom ≫ (U.comparison h).hom.app (Y, X) =
      (U.comparison h).hom.app (X, Y) ≫
        (β j ((S.T h).obj X) ((S.T h).obj Y)).hom)

private def braidingAt (X Y : S.PairCategory) (L : I)
    (hS : join X.stage Y.stage ≤ L) (hT : join Y.stage X.stage ≤ L) :
    (output U join left right (X, Y)).toStage hS ≅
      (output U join left right (Y, X)).toStage hT :=
  endpoint U join left right (X, Y) hS ≪≫
    β L (X.toStage ((left _ _).trans hS)) (Y.toStage ((right _ _).trans hS)) ≪≫
    (endpoint U join left right (Y, X) hT).symm

omit [IsDirectedOrder I] in
include hn hc in
private theorem braidingAt_transport (X Y : S.PairCategory) {L H : I}
    (hS : join X.stage Y.stage ≤ L) (hT : join Y.stage X.stage ≤ L) (k : L ≤ H) :
    S.tr k (braidingAt S U join left right β X Y L hS hT).hom =
      (braidingAt S U join left right β X Y H (hS.trans k) (hT.trans k)).hom := by
  apply (cancel_epi ((S.assoc hS k).hom.app
    (output U join left right (X, Y)).obj)).1
  apply (cancel_mono (endpoint U join left right (Y, X) (hT.trans k)).hom).1
  dsimp only [StageSystem.tr, braidingAt, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [endpoint_tower S U join left right Y X hT k]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_map_assoc]
  rw [reassoc_of% (hc k _ _)]
  simp only [Category.assoc]
  erw [← hn H
    ((S.assoc ((left _ _).trans hS) k).hom.app X.obj)
    ((S.assoc ((right _ _).trans hS) k).hom.app Y.obj)]
  erw [reassoc_of% (endpoint_tower S U join left right X Y hS k)]

include hn hc in
/-- Scalar-compatible braidings give isomorphisms with the prescribed representative at
all common stages. Source: the common-stage quotient calculation in the
paper constraints node, steps 2–4 (derived-tensor context: Stacks 06YS, 07A4, 0941).
(blueprint: lem-pur-stage-tensor-braiding-descent).
Proof: conjugate the finite braiding by the endpoint comparisons at one common upper
stage. Its inverse gives an inverse representative. The family tower law, the scalar
square, and naturality show that this representative transports to the identical
formula at every enlargement. Compare any two stages at a common upper stage. The
quotient calculus identifies their classes; composition and inverse identities are
computed at the original stage. -/
theorem braiding_exists (X Y : S.PairCategory) :
    ∃ e : output U join left right (X, Y) ≅ output U join left right (Y, X),
      ∀ (L : I) (hS : join X.stage Y.stage ≤ L) (hT : join Y.stage X.stage ≤ L),
        e.hom = StageSystem.PairCategory.mkHom L hS hT
          ((endpoint U join left right (X, Y) hS).hom ≫
            (β L (X.toStage ((left _ _).trans hS))
              (Y.toStage ((right _ _).trans hS))).hom ≫
            (endpoint U join left right (Y, X) hT).inv) := by
  obtain ⟨L₀, hS₀, hT₀⟩ := exists_ge_ge (join X.stage Y.stage) (join Y.stage X.stage)
  let b := braidingAt S U join left right β X Y L₀ hS₀ hT₀
  let e : output U join left right (X, Y) ≅ output U join left right (Y, X) :=
    { hom := StageSystem.PairCategory.mkHom L₀ hS₀ hT₀ b.hom
      inv := StageSystem.PairCategory.mkHom L₀ hT₀ hS₀ b.inv
      hom_inv_id := by
        rw [StageSystem.PairCategory.mkHom_comp_mkHom, b.hom_inv_id,
          ← StageSystem.PairCategory.id_eq_mkHom]
      inv_hom_id := by
        rw [StageSystem.PairCategory.mkHom_comp_mkHom, b.inv_hom_id,
          ← StageSystem.PairCategory.id_eq_mkHom] }
  refine ⟨e, ?_⟩
  intro L hS hT
  obtain ⟨H, h₀, h⟩ := exists_ge_ge L₀ L
  apply (StageSystem.PairCategory.mkHom_eq_mkHom_iff' _ _).2
  refine ⟨H, h₀, h, ?_⟩
  exact (braidingAt_transport S U join left right β hn hc X Y hS₀ hT₀ h₀).trans
    (braidingAt_transport S U join left right β hn hc X Y hS hT h).symm

end CategoryTheory.BilinearCoefficientDescent
