/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PointSystemChain
import WeilConjectures.CategoryTheory.PointSystemExtensions
import WeilConjectures.CategoryTheory.PointSystemPosetalRefine
import WeilConjectures.CategoryTheory.PointSystemSchedule

/-!
# Scheduling one-step inverse-system refinements

Source: Stacks Project, Sites, Tag 00YP, transfinite recursion on the set of requests
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A set of lifting requests can be scheduled in a nested chain of refinements.

Source: Stacks Project, Sites, Tag 00YP, the paragraph beginning "In order to circumvent
this we choose a well ordering on E"
(auxiliary; not a blueprint node).

Proof: Consider the category of strict refinements of V which preserve the two
classes. Directed unions exist in this category: form the filtered colimit of the
index posets and descend the object assignment and transition maps. Each index is in
one stage, so the union is directed; any equality of the two classes has a witness
in a stage and contradicts that stage's separation property. A lifting request is
persistent under refinement by naturality of colimit maps. If one is missing, apply
the supplied step to its current image. Replace the resulting preorder by a choice
of representatives of its antisymmetrization, retaining the original indices. This
cofinal restriction preserves the lifting witness and separation. Transfinite
iteration of this operation eventually satisfies all requests: otherwise its choices
of missing requests inject a well-order larger than A into A. Finally present the
resulting system as a chain with a single stage (the whole index poset). -/
theorem exists_pointSystem_refinement_chain
    {C : Type u} [Category.{v} C]
    {J : Type w} [PartialOrder J] [Nonempty J] [IsDirectedOrder J]
    (V : J ⥤ Cᵒᵖ) (P : Cᵒᵖ ⥤ Type (max w t))
    (s s' : colimit (V ⋙ P)) (hne : s ≠ s')
    {A : Type w} (Choices : A → Type w)
    (Q : A → Cᵒᵖ ⥤ Type w) (R : ∀ d, Choices d → Cᵒᵖ ⥤ Type w)
    (q : ∀ d k, R d k ⟶ Q d) (x : ∀ d, colimit (V ⋙ Q d))
    (step : ∀ {L : Type w} [Preorder L] [Nonempty L] [IsDirected L (· ≤ ·)]
      (T : L ⥤ Cᵒᵖ) (t t' : colimit (T ⋙ P)), t ≠ t' →
      ∀ (d : A) (y : colimit (T ⋙ Q d)),
      ∃ (M : Type w) (_ : Preorder M) (_ : Nonempty M)
        (_ : IsDirected M (· ≤ ·)) (S : M ⥤ Cᵒᵖ) (e : L ↪o M)
        (h : T = e.monotone.functor ⋙ S),
        pointSystemRefinementMapOfPreorder T S e h P t ≠
          pointSystemRefinementMapOfPreorder T S e h P t' ∧
        ∃ (k : Choices d) (z : colimit (S ⋙ R d k)),
          colimMap (S.whiskerLeft (q d k)) z =
            pointSystemRefinementMapOfPreorder T S e h (Q d) y) :
    ∃ c : PointSystemChain V,
      (∀ a, pointSystemRefinementMapOfPreorder V (c.stageDiagram a) (c.stageEmbedding a)
        (c.stageRestriction a) P s ≠
          pointSystemRefinementMapOfPreorder V (c.stageDiagram a) (c.stageEmbedding a)
            (c.stageRestriction a) P s') ∧
      ∀ d, ∃ (a : c.Stage) (k : Choices d) (z : colimit (c.stageDiagram a ⋙ R d k)),
        colimMap ((c.stageDiagram a).whiskerLeft (q d k)) z =
          pointSystemRefinementMapOfPreorder V (c.stageDiagram a) (c.stageEmbedding a)
            (c.stageRestriction a) (Q d) (x d) := by
  classical
  let X : PointSystemDiagram.{u, v, w} Cᵒᵖ := ⟨PartOrdEmb.of J, V⟩
  let D := PointSystemDiagram.Extension.GoodExtension X P s s'
  have : Nonempty D := ⟨⟨Under.mk (𝟙 X), by
    refine ⟨inferInstanceAs (Nonempty J), inferInstanceAs (IsDirectedOrder J), ?_⟩
    change (𝟙 X : X ⟶ X).colimitMap P s ≠ (𝟙 X : X ⟶ X).colimitMap P s'
    rw [PointSystemDiagram.Hom.colimitMap_id]
    exact hne⟩⟩
  let Satisfied (Y : D) (d : A) : Prop :=
    ∃ (k : Choices d) (z : colimit (Y.obj.right.diagram ⋙ R d k)),
      colimMap (Y.obj.right.diagram.whiskerLeft (q d k)) z = Y.obj.map (Q d) (x d)
  have persist {Y Z : D} (f : Y ⟶ Z) (d : A) (hy : Satisfied Y d) :
      Satisfied Z d := by
    obtain ⟨k, z, hz⟩ := hy
    refine ⟨k, f.hom.right.colimitMap (R d k) z, ?_⟩
    calc
      _ = f.hom.right.colimitMap (Q d)
          (colimMap (Y.obj.right.diagram.whiskerLeft (q d k)) z) :=
        (ConcreteCategory.congr_hom (pointSystemRefinementMapOfPreorder_naturality _ _
          f.hom.right.embedding.hom f.hom.right.restriction (q d k)) z).symm
      _ = _ := by
        rw [hz]
        exact ConcreteCategory.congr_hom
          (PointSystemDiagram.Extension.map_comp f.hom (Q d)) (x d)
  have extend (Y : D) (hy : ¬ ∀ d, Satisfied Y d) :
      ∃ (Z : D) (_ : Y ⟶ Z) (d : A), ¬ Satisfied Y d ∧ Satisfied Z d := by
    obtain ⟨d, hd⟩ := not_forall.mp hy
    have := Y.property.1
    have := Y.property.2.1
    obtain ⟨M, hM, hn, hdir, T, e, h, hne', k, z, hz⟩ :=
      step Y.obj.right.diagram (Y.obj.map P s) (Y.obj.map P s') Y.property.2.2
        d (Y.obj.map (Q d) (x d))
    obtain ⟨N, hN, hnonempty, hdirected, U, e', h', hsep, z', hz'⟩ :=
      exists_pointSystem_posetal_refine Y.obj.right.diagram T e h P
        (Y.obj.map P s) (Y.obj.map P s') hne' (R d k) (Q d) (q d k)
        (Y.obj.map (Q d) (x d)) z hz
    let T' : PointSystemDiagram.{u, v, w} Cᵒᵖ := ⟨PartOrdEmb.of N, U⟩
    let f : Y.obj.right ⟶ T' := ⟨PartOrdEmb.ofHom e', h'⟩
    let Z : PointSystemDiagram.Extension X := Under.mk (Y.obj.hom ≫ f)
    have hgood : PointSystemDiagram.Extension.Good P s s' Z := by
      refine ⟨hnonempty, hdirected, ?_⟩
      change (Y.obj.hom ≫ f).colimitMap P s ≠ (Y.obj.hom ≫ f).colimitMap P s'
      rw [PointSystemDiagram.Hom.colimitMap_comp]
      exact hsep
    refine ⟨⟨Z, hgood⟩, ObjectProperty.homMk (Under.homMk f rfl), d, hd, k, z', ?_⟩
    change _ = (Y.obj.hom ≫ f).colimitMap (Q d) (x d)
    rw [PointSystemDiagram.Hom.colimitMap_comp]
    exact hz'
  obtain ⟨Y, hall⟩ := exists_object_all_requirements
    (D := D) (fun B _ _ ↦ inferInstance) Satisfied (fun f ↦ persist f) extend
  have := Y.property.1
  have := Y.property.2.1
  let c : PointSystemChain V := {
    Index := Y.obj.right.index
    indexOrder := inferInstance
    Stage := ULift.{w} (Fin 1)
    stageOrder := inferInstance
    stageNonempty := inferInstance
    stageDirected := inferInstance
    diagram := Y.obj.right.diagram
    embedding := Y.obj.embedding
    restriction := Y.obj.restriction
    stage := fun _ ↦ Set.univ
    stage_mono := fun _ _ _ _ _ ↦ Set.mem_univ _
    stage_nonempty := fun _ ↦ Set.univ_nonempty
    stage_directed := fun _ i _ j _ ↦ by
      obtain ⟨k, hi, hj⟩ := exists_ge_ge i j
      exact ⟨k, Set.mem_univ _, hi, hj⟩
    exhaustive := fun i ↦ ⟨ULift.up 0, Set.mem_univ i⟩
    original_mem := fun _ _ ↦ Set.mem_univ _ }
  have hs (a : c.Stage) :
      pointSystemRefinementMapOfPreorder V (c.stageDiagram a) (c.stageEmbedding a)
        (c.stageRestriction a) P s ≠
      pointSystemRefinementMapOfPreorder V (c.stageDiagram a) (c.stageEmbedding a)
        (c.stageRestriction a) P s' := by
    intro heq
    apply Y.property.2.2
    have hm := c.map_stage_comp a P
    exact (ConcreteCategory.congr_hom hm s).symm.trans
      ((congrArg (colimit.pre (c.diagram ⋙ P) (c.stageInclusion a).monotone.functor) heq).trans
        (ConcreteCategory.congr_hom hm s'))
  refine ⟨c, hs, ?_⟩
  intro d
  let a : c.Stage := ULift.up 0
  let g : Y.obj.right.index ↪o c.stage a :=
    ⟨⟨fun i ↦ ⟨i, Set.mem_univ i⟩, fun _ _ h ↦ congrArg Subtype.val h⟩, Iff.rfl⟩
  have hg : Y.obj.right.diagram = g.monotone.functor ⋙ c.stageDiagram a := by
    refine Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
    congr 1
  have he : Y.obj.embedding.trans g = c.stageEmbedding a := by ext j; rfl
  have hm := pointSystemRefinementMapOfPreorder_comp V Y.obj.right.diagram (c.stageDiagram a)
    Y.obj.embedding g Y.obj.restriction hg (Q d)
  simp only [he] at hm
  obtain ⟨k, z, hz⟩ := hall d
  refine ⟨a, k, pointSystemRefinementMapOfPreorder _ _ g hg (R d k) z, ?_⟩
  calc
    _ = pointSystemRefinementMapOfPreorder _ _ g hg (Q d)
        (colimMap (Y.obj.right.diagram.whiskerLeft (q d k)) z) :=
      (ConcreteCategory.congr_hom
        (pointSystemRefinementMapOfPreorder_naturality _ _ g hg (q d k)) z).symm
    _ = _ := by
      rw [hz]
      exact ConcreteCategory.congr_hom hm (x d)

end CategoryTheory
