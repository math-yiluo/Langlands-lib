/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.PointSystemRefinementMap
public import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.PointSystemRefine
import WeilConjectures.CategoryTheory.PointSystemRefinementChainExists

/-!
# Simultaneous refinement of an inverse system on a site

Source: Stacks Project, Sites, Tag 00YP, Lemma `lemma-refine-all-at-once`
(auxiliary; not a blueprint node).

An inverse system is encoded covariantly in the opposite category. An order embedding
identifies the old index set with a subset carrying the induced order; equality of the
restricted functor keeps both its objects and transitions unchanged.
-/

@[expose] public section

universe u v w t r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 00YP, Lemma `lemma-refine-all-at-once`
(auxiliary; not a blueprint node).
For a sheaf and two distinct germs in a directed inverse system, there is a refinement
preserving distinctness and lifting every original germ of a representable functor through
some member of every finite covering. `uliftYoneda` only places Hom sets in the common set
universe and its elements are exactly lifted morphisms.

Proof: Form the set of finite-covering/original-Hom-germ pairs. Apply the general
refinement scheduling theorem, with the one-cover refinement Tag 00YO as its successor
step. It constructs strict refinements, retaining distinctness at limit unions by the
filtered-colimit equality criterion, and replaces preorder indices by cofinal posets
without changing the original indices. Naturality makes each lifting condition persist.
A transfinite iteration solving a missing request must terminate before a well-order
larger than the request set. Passing through its chain presentation preserves the two
distinct germs and the lifting equations. Represent the lifted Hom-colimit element at
one index; naturality of the colimit cocone gives the required composite b ≫ a k. -/
theorem exists_pointSystem_refinement_all
    {C : Type u} [Category.{v} C] (K : Precoverage C)
    (hK : K.IsSiteForCoverings)
    {J : Type (max u v)} [PartialOrder J] [Nonempty J] [IsDirectedOrder J]
    (V : J ⥤ Cᵒᵖ) (F : Sheaf K.toGrothendieck (Type (max u v w)))
    (s s' : colimit (V ⋙ F.obj)) (hne : s ≠ s') :
    ∃ (I : Type (max u v)) (_ : PartialOrder I) (_ : Nonempty I)
      (_ : IsDirectedOrder I) (U : I ⥤ Cᵒᵖ) (e : J ↪o I)
      (h : V = e.monotone.functor ⋙ U),
      pointSystemRefinementMap V U e h F.obj s ≠
        pointSystemRefinementMap V U e h F.obj s' ∧
      ∀ (n : ℕ) (W : C) (Wk : Fin n → C) (a : ∀ k, Wk k ⟶ W),
        Presieve.ofArrows Wk a ∈ K W →
        ∀ f : colimit (V ⋙ uliftYoneda.{max u v}.obj W),
          ∃ (k : Fin n) (i : I) (b : (U.obj i).unop ⟶ Wk k),
            pointSystemRefinementMap V U e h (uliftYoneda.{max u v}.obj W) f =
              colimit.ι (U ⋙ uliftYoneda.{max u v}.obj W) i (ULift.up (b ≫ a k)) := by
  classical
  simp only [pointSystemRefinementMap_eq_ofPreorder]
  let D : Type (max u v) :=
    Σ n : ℕ, Σ W : C, Σ Wk : Fin n → C,
      {a : ∀ k, Wk k ⟶ W // Presieve.ofArrows Wk a ∈ K W} ×
        colimit (V ⋙ uliftYoneda.{max u v}.obj W)
  let Choices (d : D) : Type (max u v) := ULift (Fin d.1)
  let Q (d : D) := uliftYoneda.{max u v}.obj d.2.1
  let R (d : D) (k : Choices d) := uliftYoneda.{max u v}.obj (d.2.2.1 k.down)
  let q (d : D) (k : Choices d) : R d k ⟶ Q d :=
    uliftYoneda.map (d.2.2.2.1.val k.down)
  let x (d : D) : colimit (V ⋙ Q d) := d.2.2.2.2
  obtain ⟨c, hsep, hlift⟩ :=
    exists_pointSystem_refinement_chain V F.obj s s' hne Choices Q R q x (by
      intro L _ _ _ T t t' ht d y
      rcases d with ⟨n, W, Wk, ⟨a, ha⟩, f⟩
      obtain ⟨M, hM, hnonempty, hdir, S, e, h, hne', k, z, hz⟩ :=
        pointSystemRefine K hK T.leftOp F Wk a ha t t' ht y
      refine ⟨M, hM, hnonempty, hdir, S.rightOp, e, h.symm, ?_, ?_⟩
      · rw [pointSystemRefinementMapOfPreorder_eq T S.rightOp e h.symm F.obj]
        exact hne'
      · refine ⟨ULift.up k, z, ?_⟩
        rw [pointSystemRefinementMapOfPreorder_eq T S.rightOp e h.symm (Q _)]
        exact hz)
  refine ⟨c.Index, c.indexOrder, inferInstance, inferInstance,
    c.diagram, c.embedding, c.restriction, c.ne_of_stage_ne F.obj s s' hsep, ?_⟩
  intro n W Wk a ha f
  obtain ⟨d, k, z, hz⟩ := hlift ⟨n, W, Wk, ⟨a, ha⟩, f⟩
  obtain ⟨i, b, hb⟩ := Types.jointly_surjective' z
  refine ⟨k.down, i.val, b.down, ?_⟩
  have hfac :
      colimMap (c.diagram.whiskerLeft (uliftYoneda.map (a k.down)))
          (colimit.pre (c.diagram ⋙ uliftYoneda.{max u v}.obj (Wk k.down))
            (c.stageInclusion d).monotone.functor z) =
        pointSystemRefinementMapOfPreorder V c.diagram c.embedding c.restriction
          (uliftYoneda.{max u v}.obj W) f := by
    have hm := ConcreteCategory.congr_hom
      (colimit.pre_map (c.diagram.whiskerLeft (uliftYoneda.map (a k.down)))
        (c.stageInclusion d).monotone.functor) z
    have hc := ConcreteCategory.congr_hom
      (c.map_stage_comp d (uliftYoneda.{max u v}.obj W)) f
    exact hm.trans ((congrArg
      (colimit.pre (c.diagram ⋙ uliftYoneda.{max u v}.obj W)
        (c.stageInclusion d).monotone.functor) hz).trans hc)
  rw [← hb] at hfac
  calc
    _ = _ := hfac.symm
    _ = colimMap (c.diagram.whiskerLeft (uliftYoneda.map (a k.down)))
        (colimit.ι (c.diagram ⋙ uliftYoneda.{max u v}.obj (Wk k.down)) i.val b) := by
      congr 1
      exact ConcreteCategory.congr_hom (colimit.ι_pre
        (c.diagram ⋙ uliftYoneda.{max u v}.obj (Wk k.down))
        (c.stageInclusion d).monotone.functor i) b
    _ = _ := by
      exact ConcreteCategory.congr_hom (ι_colimMap
        (c.diagram.whiskerLeft (uliftYoneda.map (a k.down))) i.val) b

end CategoryTheory
