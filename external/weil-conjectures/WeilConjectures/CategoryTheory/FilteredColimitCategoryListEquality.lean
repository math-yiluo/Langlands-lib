/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic

import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Finite diagrams and Hom descent for filtered category colimits -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem finite_stage_eq
    {J : Type z} [SmallCategory J] [IsFiltered J] (G : J ⥤ Type z)
    (c : Cocone G) (hc : IsColimit c) (n : ℕ) (j : J)
    (x y : Fin n → G.obj j) (h : ∀ q, c.ι.app j (x q) = c.ι.app j (y q)) :
    ∃ (k : J) (f : j ⟶ k), ∀ q, G.map f (x q) = G.map f (y q) := by
  classical
  induction n generalizing j with
  | zero => exact ⟨j, 𝟙 j, fun q ↦ Fin.elim0 q⟩
  | succ n ih =>
    obtain ⟨k, f, hf⟩ := ih j (fun q ↦ x q.castSucc) (fun q ↦ y q.castSucc)
      (fun q ↦ h q.castSucc)
    have he : c.ι.app k (G.map f (x (Fin.last n))) =
        c.ι.app k (G.map f (y (Fin.last n))) := by
      have hh := h (Fin.last n)
      rw [← c.w f] at hh
      exact hh
    obtain ⟨l, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc _ _).mp he
    refine ⟨l, f ≫ g, ?_⟩
    intro q
    refine Fin.lastCases ?_ (fun q ↦ ?_) q
    · simpa only [G.map_comp, ConcreteCategory.comp_apply] using hg
    · simpa only [G.map_comp, ConcreteCategory.comp_apply] using
        congrArg (fun a ↦ G.map g a) (hf q)

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph;
Categories, Section Tag 04AX.
(blueprint: lem-weil-pbc-filtered-colimit-category-list-equality).

Proof: Apply the equality criterion of filtered colimits of sets to every
pair of corresponding objects, and apply it to the arrow cocone through its
equivalence with Arrow O for every pair of corresponding arrows. This gives
finitely many common refinements, with maps out of j and k. Filteredness gives
a cocone on this finite family of refinements and their maps, making the maps
out of j and k common to all equations. Transition functors preserve the
object and arrow equalities, so all equalities hold in that cocone's apex.
For empty lists choose any common successor of j and k. -/
theorem filteredColimit_category_list_equality
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z}) :
    let O := colimit (F ⋙ Cat.objects)
    ∀ (_s : Category.{z} O) (V : ∀ j : J, F.obj j ⥤ O),
      ((∀ (j : J) (X : F.obj j), (V j).obj X = colimit.ι (F ⋙ Cat.objects) j X) ∧
      (∀ (j k : J) (f : j ⟶ k), (F.map f).toFunctor ⋙ V k = V j) ∧
      (∃ (a : Cocone (F ⋙ Cat.arrows)) (e : a.pt ≃ Arrow O),
        Nonempty (IsColimit a) ∧
          ∀ (j : J) (f : Arrow (F.obj j)),
            e (a.ι.app j f) = (V j).mapArrow.obj f)) →
      (∀ (n m : ℕ) (j k : J)
        (Xj : Fin n → F.obj j) (Xk : Fin n → F.obj k)
        (Aj : Fin m → Arrow (F.obj j)) (Ak : Fin m → Arrow (F.obj k)),
        (∀ q, (V j).obj (Xj q) = (V k).obj (Xk q)) →
        (∀ p, (V j).mapArrow.obj (Aj p) = (V k).mapArrow.obj (Ak p)) →
        ∃ (t : J) (f : j ⟶ t) (g : k ⟶ t),
          (∀ q, (F.map f).toFunctor.obj (Xj q) = (F.map g).toFunctor.obj (Xk q)) ∧
          (∀ p, (F.map f).toFunctor.mapArrow.obj (Aj p) =
            (F.map g).toFunctor.mapArrow.obj (Ak p))) := by
  classical
  intro O s V h n m j k Xj Xk Aj Ak hx ha
  obtain ⟨a, e, ⟨hc⟩, he⟩ := h.2.2
  let t := IsFiltered.max j k
  let f := IsFiltered.leftToMax j k
  let g := IsFiltered.rightToMax j k
  have hvf : ∀ b : Arrow (F.obj j),
      (V t).mapArrow.obj ((F.map f).toFunctor.mapArrow.obj b) = (V j).mapArrow.obj b := by
    intro b
    exact congrArg (fun H : F.obj j ⥤ O ↦ H.mapArrow.obj b) (h.2.1 j t f)
  have hvg : ∀ b : Arrow (F.obj k),
      (V t).mapArrow.obj ((F.map g).toFunctor.mapArrow.obj b) = (V k).mapArrow.obj b := by
    intro b
    exact congrArg (fun H : F.obj k ⥤ O ↦ H.mapArrow.obj b) (h.2.1 k t g)
  have ho : ∀ q, colimit.ι (F ⋙ Cat.objects) t ((F.map f).toFunctor.obj (Xj q)) =
      colimit.ι (F ⋙ Cat.objects) t ((F.map g).toFunctor.obj (Xk q)) := by
    intro q
    rw [← h.1, ← h.1]
    have hf := congrArg (fun H : F.obj j ⥤ O ↦ H.obj (Xj q)) (h.2.1 j t f)
    have hg := congrArg (fun H : F.obj k ⥤ O ↦ H.obj (Xk q)) (h.2.1 k t g)
    exact hf.trans ((hx q).trans hg.symm)
  obtain ⟨u, r, hr⟩ := finite_stage_eq (F ⋙ Cat.objects)
    (colimit.cocone (F ⋙ Cat.objects)) (colimit.isColimit (F ⋙ Cat.objects)) n t
    (fun q ↦ (F.map f).toFunctor.obj (Xj q))
    (fun q ↦ (F.map g).toFunctor.obj (Xk q)) ho
  have har : ∀ p, a.ι.app u
      ((F.map r).toFunctor.mapArrow.obj ((F.map f).toFunctor.mapArrow.obj (Aj p))) =
      a.ι.app u
      ((F.map r).toFunctor.mapArrow.obj ((F.map g).toFunctor.mapArrow.obj (Ak p))) := by
    intro p
    apply e.injective
    rw [he, he]
    have hu := h.2.1 t u r
    have h1 := congrArg (fun H : F.obj t ⥤ O ↦
      H.mapArrow.obj ((F.map f).toFunctor.mapArrow.obj (Aj p))) hu
    have h2 := congrArg (fun H : F.obj t ⥤ O ↦
      H.mapArrow.obj ((F.map g).toFunctor.mapArrow.obj (Ak p))) hu
    exact h1.trans ((hvf _).trans ((ha p).trans ((hvg _).symm.trans h2.symm)))
  obtain ⟨w, v, hv⟩ := finite_stage_eq (F ⋙ Cat.arrows) a hc m u
    (fun p ↦ (F.map r).toFunctor.mapArrow.obj ((F.map f).toFunctor.mapArrow.obj (Aj p)))
    (fun p ↦ (F.map r).toFunctor.mapArrow.obj ((F.map g).toFunctor.mapArrow.obj (Ak p))) har
  refine ⟨w, f ≫ r ≫ v, g ≫ r ≫ v, ?_, ?_⟩
  · intro q
    have hh := congrArg (fun x ↦ (F.map v).toFunctor.obj x) (hr q)
    change (F.map v).toFunctor.obj ((F.map r).toFunctor.obj ((F.map f).toFunctor.obj (Xj q))) =
      (F.map v).toFunctor.obj ((F.map r).toFunctor.obj ((F.map g).toFunctor.obj (Xk q))) at hh
    simpa only [F.map_comp, Cat.Hom.comp_toFunctor, Functor.comp_obj] using hh
  · intro p
    have hh := hv p
    change (F.map v).toFunctor.mapArrow.obj
      ((F.map r).toFunctor.mapArrow.obj ((F.map f).toFunctor.mapArrow.obj (Aj p))) =
      (F.map v).toFunctor.mapArrow.obj
      ((F.map r).toFunctor.mapArrow.obj ((F.map g).toFunctor.mapArrow.obj (Ak p))) at hh
    simpa only [F.map_comp, Cat.Hom.comp_toFunctor, Functor.mapArrow_obj,
      Arrow.mk_hom, Functor.comp_map] using hh

end CategoryTheory
