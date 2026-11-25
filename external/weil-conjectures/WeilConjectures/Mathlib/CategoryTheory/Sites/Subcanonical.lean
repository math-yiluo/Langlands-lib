/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Sections of single-morphism covers

In a subcanonical site, if evaluation at an object `W` sends epimorphisms of sheaves of types to
surjections, then every morphism `f : V ⟶ W` generating a covering sieve has a section: the
morphism of representable sheaves induced by `f` is locally surjective, hence an epimorphism,
and a preimage of `𝟙 W` is a section of `f`.
-/

@[expose] public section

universe w v u

open Opposite

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [J.Subcanonical]

/-- If evaluation at `W` sends epimorphisms of sheaves of types to surjections, then every
morphism `f : V ⟶ W` generating a covering sieve of `W` has a section. -/
lemma exists_comp_eq_id_of_surjective_app {V W : C} (f : V ⟶ W)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J W)
    (hW : ∀ (F G : Sheaf J (Type (max v w))) (e : F ⟶ G), Epi e →
      Function.Surjective (e.hom.app (op W))) :
    ∃ s : W ⟶ V, s ≫ f = 𝟙 W := by
  let e := J.uliftYoneda.{w}.map f
  have : Sheaf.IsLocallySurjective e := ⟨fun {X} s ↦ by
    refine J.superset_covering ?_ (J.pullback_stable s.down hf)
    rintro Y g ⟨Z, a, b, ⟨⟩, h⟩
    exact ⟨ULift.up a, congrArg ULift.up h⟩⟩
  obtain ⟨t, ht⟩ := hW _ _ e inferInstance (ULift.up (𝟙 W))
  exact ⟨t.down, congrArg ULift.down ht⟩

end CategoryTheory.GrothendieckTopology
