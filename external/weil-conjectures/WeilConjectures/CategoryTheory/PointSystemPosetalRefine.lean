/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Order.Directed
public import WeilConjectures.CategoryTheory.PointSystemRefinementMap
import WeilConjectures.CategoryTheory.PointSystemPosetalReplacement
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Types.Basic

/-!
# Retaining lifting witnesses in a posetal refinement

Source: Stacks Project, Sites, Tag 00YP (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w t

open CategoryTheory Limits

namespace CategoryTheory

/-- A preorder refinement of a partial order can be replaced by a partial order,
retaining the embedding, separation and a prescribed lifting witness.

Source: Stacks Project, Sites, Tag 00YP, relabelling the refinements before taking unions
(auxiliary; not a blueprint node).
Proof: Choose representatives of the antisymmetrization, retaining each original index.
The representatives are cofinal. Restrict the diagram to them. The canonical colimit map
is an isomorphism, so the lift has a unique inverse image. Naturality and composition of
refinement maps transfer the lifting equation; distinctness follows by mapping back. -/
theorem exists_pointSystem_posetal_refine
    {C : Type u} [Category.{v} C]
    {J M : Type w} [PartialOrder J] [Nonempty J] [Preorder M]
    [IsDirected M (· ≤ ·)] (V : J ⥤ Cᵒᵖ) (S : M ⥤ Cᵒᵖ) (e : J ↪o M)
    (h : V = e.monotone.functor ⋙ S)
    (P : Cᵒᵖ ⥤ Type (max w t)) (s s' : colimit (V ⋙ P))
    (hne : pointSystemRefinementMapOfPreorder V S e h P s ≠
      pointSystemRefinementMapOfPreorder V S e h P s')
    (R Q : Cᵒᵖ ⥤ Type w) (q : R ⟶ Q) (y : colimit (V ⋙ Q))
    (z : colimit (S ⋙ R))
    (hz : colimMap (S.whiskerLeft q) z = pointSystemRefinementMapOfPreorder V S e h Q y) :
    ∃ (N : Type w) (_ : PartialOrder N) (_ : Nonempty N) (_ : IsDirectedOrder N)
      (U : N ⥤ Cᵒᵖ) (d : J ↪o N) (g : V = d.monotone.functor ⋙ U),
      pointSystemRefinementMapOfPreorder V U d g P s ≠
        pointSystemRefinementMapOfPreorder V U d g P s' ∧
      ∃ z' : colimit (U ⋙ R),
        colimMap (U.whiskerLeft q) z' = pointSystemRefinementMapOfPreorder V U d g Q y := by
  classical
  obtain ⟨N, hN, hn, hd, r, d, he, hcofinal⟩ := exists_pointSystem_posetal_replacement e
  let U := r.monotone.functor ⋙ S
  have g : V = d.monotone.functor ⋙ U := h.trans (by rw [← he]; rfl)
  have hcomp (B : Cᵒᵖ ⥤ Type (max w t)) :
      pointSystemRefinementMapOfPreorder V U d g B ≫
          pointSystemRefinementMapOfPreorder U S r rfl B =
        pointSystemRefinementMapOfPreorder V S e h B := by
    simpa only [he] using pointSystemRefinementMapOfPreorder_comp V U S d r g rfl B
  have hcompQ : pointSystemRefinementMapOfPreorder V U d g Q ≫
      pointSystemRefinementMapOfPreorder U S r rfl Q =
        pointSystemRefinementMapOfPreorder V S e h Q := by
    simpa only [he] using pointSystemRefinementMapOfPreorder_comp V U S d r g rfl Q
  have : r.monotone.functor.Final :=
    r.monotone.final_functor_iff.mpr (fun i ↦ (hcofinal i).imp fun _ h ↦ h.1)
  let z' := inv (colimit.pre (S ⋙ R) r.monotone.functor) z
  have hz' : pointSystemRefinementMapOfPreorder U S r rfl R z' = z := by
    rw [pointSystemRefinementMapOfPreorder_eq U S r rfl R]
    simp only [eqToHom_refl, Category.id_comp]
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id (colimit.pre (S ⋙ R) r.monotone.functor)) z
  refine ⟨N, hN, hn, hd, U, d, g, ?_, z', ?_⟩
  · intro heq
    apply hne
    exact (ConcreteCategory.congr_hom (hcomp P) s).symm.trans
      ((congrArg (pointSystemRefinementMapOfPreorder U S r rfl P) heq).trans
        (ConcreteCategory.congr_hom (hcomp P) s'))
  · have hm : pointSystemRefinementMapOfPreorder U S r rfl Q =
        colimit.pre (S ⋙ Q) r.monotone.functor := by
      simp only [pointSystemRefinementMapOfPreorder_eq U S r rfl Q, eqToHom_refl, Category.id_comp]
    apply (mono_iff_injective (colimit.pre (S ⋙ Q) r.monotone.functor)).mp inferInstance
    rw [← hm]
    calc
      _ = colimMap (S.whiskerLeft q) z := by
        rw [← hz']
        exact ConcreteCategory.congr_hom
          (pointSystemRefinementMapOfPreorder_naturality U S r rfl q) z'
      _ = _ := hz
      _ = _ := (ConcreteCategory.congr_hom hcompQ y).symm

end CategoryTheory
