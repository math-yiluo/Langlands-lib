/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Comparison of reduction towers from universal units

Let `RC : C ⥤ ℕᵒᵖ ⥤ C` and `RD : D ⥤ ℕᵒᵖ ⥤ D` be towers of reflections with units
`ηC` and `ηD`, and let `E : C ⥤ D`. If every unit of `RD` is universal among maps into a
class of objects containing the values of `E` on the levels of `RC`, and the images under
`E` of the units of `RC` are universal for the same class, then `E` commutes with the
towers by a unique isomorphism compatible with the units.

Source: Stacks Project, Categories, Tag 0036 (uniqueness of universal arrows)
(auxiliary; not a blueprint node).
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D]

/-- A left adjoint carries an arrow universal for maps into the image of the right adjoint
to an arrow universal for the corresponding maps.
Source: Stacks Project, Categories, Tag 0036 (auxiliary; not a blueprint node). -/
theorem existsUnique_comp_map_of_adjunction {E : C ⥤ D} {G : D ⥤ C} (adj : E ⊣ G)
    {M R : C} (η : M ⟶ R) (Q : D) (h : ∀ f : M ⟶ G.obj Q, ∃! g : R ⟶ G.obj Q, η ≫ g = f)
    (f : E.obj M ⟶ Q) : ∃! g : E.obj R ⟶ Q, E.map η ≫ g = f := by
  obtain ⟨g, hg, hu⟩ := h (adj.homEquiv _ _ f)
  refine ⟨(adj.homEquiv _ _).symm g, ?_, ?_⟩
  · dsimp only
    rw [← adj.homEquiv_naturality_left_symm, hg, Equiv.symm_apply_apply]
  · intro g' hg'
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply hu
    rw [← adj.homEquiv_naturality_left, hg']

/-- Units of a tower of reflections commuting with a functor determine a unique tower
isomorphism, provided they are universal for the same class of targets.
Source: Stacks Project, Categories, Tag 0036 (auxiliary; not a blueprint node). -/
theorem existsUnique_tower_iso_of_universal (E : C ⥤ D)
    (RC : C ⥤ ℕᵒᵖ ⥤ C) (ηC : Functor.const ℕᵒᵖ ⟶ RC)
    (RD : D ⥤ ℕᵒᵖ ⥤ D) (ηD : Functor.const ℕᵒᵖ ⟶ RD) (K : ℕ → D → Prop)
    (hK : ∀ n P, K n P → K (n + 1) P)
    (ha : ∀ n N, K n ((RD.obj N).obj (op n)))
    (hb : ∀ n (N P : D), K n P → ∀ f : N ⟶ P,
      ∃! g : (RD.obj N).obj (op n) ⟶ P, (ηD.app N).app (op n) ≫ g = f)
    (hc : ∀ n M, K n (E.obj ((RC.obj M).obj (op n))))
    (hd : ∀ n M (Q : D), K n Q → ∀ f : E.obj M ⟶ Q,
      ∃! g : E.obj ((RC.obj M).obj (op n)) ⟶ Q, E.map ((ηC.app M).app (op n)) ≫ g = f) :
    ∃! e : E ⋙ RD ≅ RC ⋙ (Functor.whiskeringRight ℕᵒᵖ C D).obj E,
      ∀ M n, (ηD.app (E.obj M)).app (op n) ≫ (e.hom.app M).app (op n) =
        E.map ((ηC.app M).app (op n)) := by
  -- the level maps and their inverses
  let u (M : C) (n : ℕ) := (hb n (E.obj M) _ (hc n M) (E.map ((ηC.app M).app (op n)))).exists
  let v (M : C) (n : ℕ) := (hd n M _ (ha n (E.obj M)) ((ηD.app (E.obj M)).app (op n))).exists
  let f (M : C) (n : ℕ) := (u M n).choose
  let g (M : C) (n : ℕ) := (v M n).choose
  have hf (M : C) (n : ℕ) : (ηD.app (E.obj M)).app (op n) ≫ f M n =
      E.map ((ηC.app M).app (op n)) := (u M n).choose_spec
  have hg (M : C) (n : ℕ) : E.map ((ηC.app M).app (op n)) ≫ g M n =
      (ηD.app (E.obj M)).app (op n) := (v M n).choose_spec
  have hfg (M : C) (n : ℕ) : f M n ≫ g M n = 𝟙 _ := by
    have h := hb n (E.obj M) _ (ha n (E.obj M)) ((ηD.app (E.obj M)).app (op n))
    exact h.unique (by rw [← Category.assoc, hf, hg]) (Category.comp_id _)
  have hgf (M : C) (n : ℕ) : g M n ≫ f M n = 𝟙 _ := by
    have h := hd n M _ (hc n M) (E.map ((ηC.app M).app (op n)))
    exact h.unique (by rw [← Category.assoc, hg, hf]) (Category.comp_id _)
  -- naturality in the tower index
  have hfn (M : C) (n : ℕ) :
      f M (n + 1) ≫ E.map ((RC.obj M).map (homOfLE (Nat.le_succ n)).op) =
        (RD.obj (E.obj M)).map (homOfLE (Nat.le_succ n)).op ≫ f M n := by
    have hηD := (ηD.app (E.obj M)).naturality (homOfLE (Nat.le_succ n)).op
    have hηC := (ηC.app M).naturality (homOfLE (Nat.le_succ n)).op
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hηD hηC
    apply (hb (n + 1) (E.obj M) _ (hK n _ (hc n M))
      (E.map ((ηC.app M).app (op (n + 1))) ≫
        E.map ((RC.obj M).map (homOfLE (Nat.le_succ n)).op))).unique
    · rw [← Category.assoc, hf]
    · rw [← Category.assoc, ← hηD, hf, ← E.map_comp, ← hηC]
  -- naturality in the module
  have hfm {M M' : C} (φ : M ⟶ M') (n : ℕ) :
      (RD.map (E.map φ)).app (op n) ≫ f M' n =
        f M n ≫ E.map ((RC.map φ).app (op n)) := by
    have hηD := congrArg (fun t ↦ t.app (op n)) (ηD.naturality (E.map φ))
    have hηC := congrArg (fun t ↦ t.app (op n)) (ηC.naturality φ)
    simp only [Functor.const_map_app, NatTrans.comp_app] at hηD hηC
    apply (hb n (E.obj M) _ (hc n M')
      (E.map ((ηC.app M).app (op n)) ≫ E.map ((RC.map φ).app (op n)))).unique
    · rw [← Category.assoc, ← hηD, Category.assoc, hf, ← E.map_comp, ← E.map_comp, hηC]
    · rw [← Category.assoc, hf]
  let h (M : C) : (E ⋙ RD).obj M ⟶ (RC ⋙ (Functor.whiskeringRight ℕᵒᵖ C D).obj E).obj M :=
    NatTrans.ofOpSequence (fun n ↦ f M n) (fun n ↦ (hfn M n).symm)
  have hh (M : C) (n : ℕ) : (h M).app (op n) = f M n := rfl
  have hiso (M : C) : IsIso (h M) := by
    have : ∀ n : ℕᵒᵖ, IsIso ((h M).app n) := fun n ↦
      ⟨g M n.unop, hfg M n.unop, hgf M n.unop⟩
    exact NatIso.isIso_of_isIso_app _
  let e : E ⋙ RD ≅ RC ⋙ (Functor.whiskeringRight ℕᵒᵖ C D).obj E :=
    NatIso.ofComponents (fun M ↦ asIso (h M)) (by
      intro M M' φ
      ext ⟨n⟩
      exact hfm φ n)
  refine ⟨e, fun M n ↦ hf M n, ?_⟩
  intro e' he'
  ext M ⟨n⟩
  exact (hb n (E.obj M) _ (hc n M) (E.map ((ηC.app M).app (op n)))).unique (he' M n) (hf M n)

end CategoryTheory.Functor
