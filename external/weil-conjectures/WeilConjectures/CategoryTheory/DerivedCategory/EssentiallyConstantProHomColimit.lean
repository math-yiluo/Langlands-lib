/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.CategoryTheory.Limits.Types.ColimitType

/-! # Hom out of an essentially constant pro-diagram

Source: Stacks Project, Categories, Definition 05PU(2), Lemma 05PZ;
Derived Categories, Lemma 0FND, sixth equality
(blueprint: lem-pc-essentially-constant-pro-hom-colimit).
-/

@[expose] public section

universe uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- For every cone exhibiting `D` as essentially constant with value `X` in the sense
of `IsEssentiallyConstantProDiagram`, precomposition induces a bijection from the
colimit of `Hom(D.obj j, Y)` over `Jᵒᵖ` to `Hom(X, Y)`. The representative equation
specifies the canonical map uniquely, without choosing a different cone for each `Y`.

Proof: (1) Naturality of `u` gives `D.map a ≫` compatibility: precomposing a
representative with a transition does not change its composite with `u`. Thus the
representative formula descends to the colimit. (2) Choose `j₀` and `r` from the
retraction and factorization clauses of Definition 05PU(2). For `t : X ⟶ Y`, the
representative `r ≫ t` at `j₀` maps to `t`, proving surjectivity. (3) If representatives
`f` at `j` and `g` at `k` have equal composites with the cone maps, cofilteredness gives
a common earlier stage `l`. Apply the factorization clause there to obtain an earlier
stage `m` whose transition to `l` factors through `D.obj j₀`, `r`, and `u.app l`.
The transitions of `f` and `g` to `m` are then equal by their assumed equality on `X`.
They therefore represent the same colimit element, proving injectivity. These are
exactly the three elementary steps of the node's proof; no additional proof nodes
are required.

Source: Stacks Project, Categories, Definition 05PU(2), Lemma 05PZ;
Derived Categories, Lemma 0FND, sixth equality
(blueprint: lem-pc-essentially-constant-pro-hom-colimit). -/
theorem essentiallyConstantPro_hom_colimit
    {J : Type uJ} {C : Type uC} [Category.{vJ} J] [Category.{vC} C]
    (D : J ⥤ C) (X : C) (h : IsEssentiallyConstantProDiagram D X) :
    ∀ u : (Functor.const J).obj X ⟶ D,
      (∃ j₀ : J, ∃ r : D.obj j₀ ⟶ X, u.app j₀ ≫ r = 𝟙 X ∧
        ∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
          D.map b = D.map a ≫ r ≫ u.app j) →
      ∀ Y : C, ∃ φ : (D.op ⋙ yoneda.obj Y).ColimitType → (X ⟶ Y),
        Function.Bijective φ ∧
          ∀ (j : J) (f : D.obj j ⟶ Y),
            φ ((D.op ⋙ yoneda.obj Y).ιColimitType (Opposite.op j) f) = u.app j ≫ f := by
  intro u hu Y
  have : IsCofiltered J := h.1
  obtain ⟨j₀, r, hr, hfac⟩ := hu
  let F := D.op ⋙ yoneda.obj Y
  let c : F.CoconeTypes := {
    pt := X ⟶ Y
    ι := fun j f => u.app (Opposite.unop j) ≫ f
    ι_naturality := by
      intro j j' a
      funext f
      dsimp [F]
      simpa [Category.assoc] using (congrArg (fun z => z ≫ f) (u.naturality a.unop)).symm
    }
  let φ : F.ColimitType → (X ⟶ Y) := F.descColimitType c
  refine ⟨φ, ?_, ?_⟩
  · constructor
    · intro x y hxy
      obtain ⟨j, f, rfl⟩ := F.ιColimitType_jointly_surjective x
      obtain ⟨k, g, rfl⟩ := F.ιColimitType_jointly_surjective y
      obtain ⟨l, a, b, _⟩ :=
        IsCofilteredOrEmpty.cone_objs (Opposite.unop j) (Opposite.unop k)
      obtain ⟨m, q, s, hs⟩ := hfac l
      apply F.ιColimitType_eq_of_map_eq_map f g (Opposite.op (s ≫ a))
        (Opposite.op (s ≫ b))
      dsimp [F]
      simp only [Functor.map_comp]
      simp only [Category.assoc, hs]
      change u.app (Opposite.unop j) ≫ f = u.app (Opposite.unop k) ≫ g at hxy
      calc
        D.map q ≫ r ≫ u.app l ≫ D.map a ≫ f =
            D.map q ≫ r ≫ (u.app l ≫ D.map a) ≫ f := by simp [Category.assoc]
        _ = D.map q ≫ r ≫ u.app (Opposite.unop j) ≫ f := by
          rw [show u.app l ≫ D.map a = u.app (Opposite.unop j) by
            simpa using (u.naturality a).symm]
        _ = D.map q ≫ r ≫ u.app (Opposite.unop k) ≫ g := by rw [hxy]
        _ = D.map q ≫ r ≫ (u.app l ≫ D.map b) ≫ g := by
          rw [show u.app (Opposite.unop k) = u.app l ≫ D.map b by
            simpa using (u.naturality b)]
        _ = D.map q ≫ r ≫ u.app l ≫ D.map b ≫ g := by simp [Category.assoc]
    · intro t
      exact ⟨F.ιColimitType (Opposite.op j₀) (r ≫ t), by
        dsimp [φ, c]
        rw [← Category.assoc, hr, Category.id_comp]
      ⟩
  · intro j f
    rfl

end CategoryTheory
