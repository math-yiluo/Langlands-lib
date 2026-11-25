/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-! # Uniqueness of normalized derived adjunctions

Source: Stacks Project, Derived Categories, Tag 09T5.
(blueprint: lem-pc-derived-adjunction-normalization-unique).
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Adjunction

variable {C D H J : Type*} [Category* C] [Category* D] [Category* H] [Category* J]
  {T : C ⥤ D} {U : D ⥤ C} {L : H ⥤ J} {R : J ⥤ H}

private theorem normalized_counit
    (b : T ⊣ U) (a : L ⊣ R) (Q : C ⥤ H) (P : D ⥤ J)
    (ε : Q ⋙ L ⟶ T ⋙ P) (β : U ⋙ Q ⟶ P ⋙ R)
    (hc : ∀ M K (t : T.obj M ⟶ K),
      a.homEquiv (Q.obj M) (P.obj K) (ε.app M ≫ P.map t) =
        Q.map (b.homEquiv M K t) ≫ β.app K) (K : D) :
    L.map (β.app K) ≫ a.counit.app (P.obj K) =
      ε.app (U.obj K) ≫ P.map (b.counit.app K) := by
  have hid : b.homEquiv _ K (b.counit.app K) = 𝟙 _ :=
    b.right_triangle_components K
  have h := hc _ K (b.counit.app K)
  rw [hid, Q.map_id, Category.id_comp] at h
  have h' := congrArg (a.homEquiv _ _).symm h
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply] using h'.symm

/-- The representative Hom formula determines an adjunction on fixed derived functors.
The only absoluteness needed here is the right-derived property of `R ⋙ L`.

Proof: apply each representative formula to the underived counit. The underived
triangle identity gives the right-derived unit, and inverse transposition gives
`L(β) ≫ counit = ε ≫ P(underived counit)`. Thus both counits have the same composite
with the unit of the right-derived functor `R ⋙ L`. Its universal property makes
the two natural transformations equal. An adjunction is determined by its counit.
The argument works for zero objects, empty categories, and identity functors.
Source: Stacks Project, Derived Categories, Tag 09T5
(blueprint: lem-pc-derived-adjunction-normalization-unique). -/
theorem eq_of_normalization
    (b : T ⊣ U) (a a' : L ⊣ R) (Q : C ⥤ H) (P : D ⥤ J)
    (ε : Q ⋙ L ⟶ T ⋙ P) (β : U ⋙ Q ⟶ P ⋙ R) (W : MorphismProperty D)
    [P.IsLocalization W]
    [(R ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight β L ≫ (Functor.associator P R L).hom) W]
    (ha : ∀ M K (t : T.obj M ⟶ K),
      a.homEquiv (Q.obj M) (P.obj K) (ε.app M ≫ P.map t) =
        Q.map (b.homEquiv M K t) ≫ β.app K)
    (ha' : ∀ M K (t : T.obj M ⟶ K),
      a'.homEquiv (Q.obj M) (P.obj K) (ε.app M ≫ P.map t) =
        Q.map (b.homEquiv M K t) ≫ β.app K) : a = a' := by
  apply Adjunction.ext_counit
  apply (R ⋙ L).rightDerived_ext
    (Functor.whiskerRight β L ≫ (Functor.associator P R L).hom) W
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.comp_id]
  exact (normalized_counit b a Q P ε β ha K).trans
    (normalized_counit b a' Q P ε β ha' K).symm

end CategoryTheory.Adjunction
