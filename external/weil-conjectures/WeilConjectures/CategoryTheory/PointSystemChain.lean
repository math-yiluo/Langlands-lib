/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PointSystemRefinementMap
public import Mathlib.Order.Directed
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Directed unions of nested inverse systems

Source: Stacks Project, Sites, Tag 00YP, the union of a chain of refinements
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A nested family of directed subsystems with a fixed original subsystem.
The ambient index has not yet been asserted to be directed. -/
structure PointSystemChain {C : Type u} [Category.{v} C]
    {J : Type w} [PartialOrder J] (V : J ⥤ Cᵒᵖ) where
  Index : Type w
  indexOrder : PartialOrder Index
  Stage : Type w
  stageOrder : PartialOrder Stage
  stageNonempty : Nonempty Stage
  stageDirected : IsDirectedOrder Stage
  diagram : Index ⥤ Cᵒᵖ
  embedding : J ↪o Index
  restriction : V = embedding.monotone.functor ⋙ diagram
  stage : Stage → Set Index
  stage_mono : Monotone stage
  stage_nonempty : ∀ a, (stage a).Nonempty
  stage_directed : ∀ a, DirectedOn (· ≤ ·) (stage a)
  exhaustive : ∀ i, ∃ a, i ∈ stage a
  original_mem : ∀ a j, embedding j ∈ stage a

attribute [instance] PointSystemChain.indexOrder PointSystemChain.stageOrder
  PointSystemChain.stageNonempty PointSystemChain.stageDirected

namespace PointSystemChain

variable {C : Type u} [Category.{v} C]
  {J : Type w} [PartialOrder J] {V : J ⥤ Cᵒᵖ} (c : PointSystemChain V)

instance (a : c.Stage) : Nonempty (c.stage a) := (c.stage_nonempty a).to_subtype

instance (a : c.Stage) : IsDirectedOrder (c.stage a) :=
  (c.stage_directed a).isDirectedOrder

instance : Nonempty c.Index := by
  obtain ⟨a⟩ := c.stageNonempty
  obtain ⟨i, _⟩ := c.stage_nonempty a
  exact ⟨i⟩

instance : IsDirectedOrder c.Index where
  directed i j := by
    obtain ⟨a, hi⟩ := c.exhaustive i
    obtain ⟨b, hj⟩ := c.exhaustive j
    obtain ⟨d, ha, hb⟩ := exists_ge_ge a b
    obtain ⟨k, _, hik, hjk⟩ :=
      c.stage_directed d i (c.stage_mono ha hi) j (c.stage_mono hb hj)
    exact ⟨k, hik, hjk⟩

/-- Inclusion of one stage in the union. -/
def stageInclusion (a : c.Stage) : c.stage a ↪o c.Index where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

/-- The diagram restricted to one stage. -/
def stageDiagram (a : c.Stage) : c.stage a ⥤ Cᵒᵖ :=
  (c.stageInclusion a).monotone.functor ⋙ c.diagram

/-- The original index embeds in every stage. -/
def stageEmbedding (a : c.Stage) : J ↪o c.stage a where
  toFun j := ⟨c.embedding j, c.original_mem a j⟩
  inj' _ _ h := c.embedding.injective (congrArg Subtype.val h)
  map_rel_iff' := c.embedding.map_rel_iff

/-- The original diagram is unchanged in every stage. -/
theorem stageRestriction (a : c.Stage) :
    V = (c.stageEmbedding a).monotone.functor ⋙ c.stageDiagram a := by
  exact c.restriction

/-- Passing through a stage gives the canonical map into the union. -/
theorem map_stage_comp (a : c.Stage) (P : Cᵒᵖ ⥤ Type (max w t)) :
    pointSystemRefinementMapOfPreorder V (c.stageDiagram a) (c.stageEmbedding a)
        (c.stageRestriction a) P ≫
      colimit.pre (c.diagram ⋙ P) (c.stageInclusion a).monotone.functor =
        pointSystemRefinementMapOfPreorder V c.diagram c.embedding c.restriction P := by
  have h := pointSystemRefinementMapOfPreorder_comp V (c.stageDiagram a) c.diagram
      (c.stageEmbedding a) (c.stageInclusion a) (c.stageRestriction a) rfl P
  rw [pointSystemRefinementMapOfPreorder_eq (c.stageDiagram a) c.diagram
    (c.stageInclusion a) rfl P] at h
  have he : (c.stageEmbedding a).trans (c.stageInclusion a) = c.embedding := by
    ext j
    rfl
  simpa only [eqToHom_refl, Category.id_comp, he] using h

/-- Equality in the union is already witnessed in a stage containing the witnesses.
Source: Stacks Project, Sites, Tag 00YP, condition (2) for a union of refinements
(auxiliary; not a blueprint node). -/
theorem ne_of_stage_ne [Nonempty J] [IsDirectedOrder J]
    (P : Cᵒᵖ ⥤ Type (max w t)) (s s' : colimit (V ⋙ P))
    (hne : ∀ a, pointSystemRefinementMapOfPreorder V (c.stageDiagram a) (c.stageEmbedding a)
      (c.stageRestriction a) P s ≠
        pointSystemRefinementMapOfPreorder V (c.stageDiagram a) (c.stageEmbedding a)
          (c.stageRestriction a) P s') :
    pointSystemRefinementMapOfPreorder V c.diagram c.embedding c.restriction P s ≠
      pointSystemRefinementMapOfPreorder V c.diagram c.embedding c.restriction P s' := by
  obtain ⟨j, x, y, rfl, rfl⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ (colimit.isColimit (V ⋙ P)) s s'
  intro heq
  have rep (z : (V ⋙ P).obj j) :
      pointSystemRefinementMapOfPreorder V c.diagram c.embedding c.restriction P
          (colimit.ι (V ⋙ P) j z) =
        colimit.ι (c.diagram ⋙ P) (c.embedding j)
          (P.map (eqToHom (congrArg (fun T : J ⥤ Cᵒᵖ ↦ T.obj j) c.restriction)) z) :=
    ConcreteCategory.congr_hom
      (pointSystemRefinementMapOfPreorder_ι V c.diagram c.embedding c.restriction P j) z
  have heq' := (rep x).symm.trans (heq.trans (rep y))
  obtain ⟨i, f, g, hi⟩ := (Types.FilteredColimit.colimit_eq_iff _).mp heq'
  obtain ⟨a, hia⟩ := c.exhaustive i
  have rep' (z : (V ⋙ P).obj j) :
      pointSystemRefinementMapOfPreorder V (c.stageDiagram a) (c.stageEmbedding a)
          (c.stageRestriction a) P (colimit.ι (V ⋙ P) j z) =
        colimit.ι (c.stageDiagram a ⋙ P) ((c.stageEmbedding a) j)
          (P.map (eqToHom (congrArg (fun T : J ⥤ Cᵒᵖ ↦ T.obj j) c.restriction)) z) :=
    ConcreteCategory.congr_hom (pointSystemRefinementMapOfPreorder_ι V (c.stageDiagram a)
      (c.stageEmbedding a) (c.stageRestriction a) P j) z
  apply hne a
  apply (rep' x).trans
  apply Eq.trans _ (rep' y).symm
  apply (Types.FilteredColimit.colimit_eq_iff _).mpr
  exact ⟨⟨i, hia⟩, homOfLE (leOfHom f), homOfLE (leOfHom g), hi⟩

end PointSystemChain

end CategoryTheory
