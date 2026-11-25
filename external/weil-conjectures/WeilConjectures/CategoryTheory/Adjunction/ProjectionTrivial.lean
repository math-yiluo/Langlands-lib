/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionRefinement

/-!

# Projection morphisms of trivial adjunctions

This file collects formal facts about projection morphisms and projection comparisons used for
the projection formula of a proper morphism, computed through its trivial compactification
`X ⟶[𝟙] X ⟶[f] Y` (blueprint `prop-sf-pf-coherence`).

- `CategoryTheory.Adjunction.id_projectionComparison`: the projection comparison of the identity
  adjunction is the identity.
- `CategoryTheory.Adjunction.projectionComparison_comp_whiskerRight_of_iso_id`: for an adjunction
  `I ⊣ Is` with an identification `α : I ≅ 𝟭` and the conjugate `b : Is ⟶ 𝟭` of `α⁻¹`, if `b` is
  monoidal, the projection comparison is read off from `α` and `b`.
- `CategoryTheory.Adjunction.trivialOpen_exceptionalProjection_comp`: for the trivial
  compactification `(𝟙, p)`, the exceptional projection morphism is the projection morphism of
  `Ps ⊣ P` through `α`.
- `CategoryTheory.Adjunction.map_comp_ofNatIsoRight_counit`: a morphism identified with the
  projection morphism through `e : G ≅ G'` has the adjoint of a projection morphism for the
  transported adjunction `(adj.ofNatIsoRight e)`.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

section Id

variable {C : Type*} [Category C] [MonoidalCategory C]

open Functor.LaxMonoidal in
/-- The projection comparison of the identity adjunction is the identity. -/
lemma id_projectionComparison (M N : C) :
    (Adjunction.id (C := C)).projectionComparison M N = 𝟙 _ := by
  rw [projectionComparison, homEquiv_counit]
  simp

end Id

section Trivial

variable {C : Type*} [Category C] [MonoidalCategory C] {I Is : C ⥤ C} [Is.Monoidal]
  (bi : I ⊣ Is) (α : I ≅ 𝟭 C) (b : ∀ W, Is.obj W ⟶ W)

omit [MonoidalCategory C] [Is.Monoidal] in
/-- For an adjunction `I ⊣ Is` with `α : I ≅ 𝟭`, the conjugate `Is ≅ 𝟭` of `α⁻¹` is the
composite `Is W ⟶ I Is W ⟶ W` of `α⁻¹` and the counit. -/
lemma conjugateIsoEquiv_id_hom_app
    (hαb : ∀ W, α.inv.app (Is.obj W) ≫ bi.counit.app W = b W) (W : C) :
    (conjugateIsoEquiv bi Adjunction.id α.symm).hom.app W = b W := by
  have h := conjugateEquiv_counit bi Adjunction.id α.symm.hom W
  simp only [Functor.id_obj, Functor.id_map, id_counit, NatTrans.id_app, Iso.symm_hom] at h
  rw [conjugateIsoEquiv_apply_hom, Iso.symm_hom, ← hαb, ← h]
  exact (Category.comp_id (((conjugateEquiv bi Adjunction.id) α.inv).app W)).symm

/-- **The projection comparison of an adjunction identified with the identity adjunction**: for
`I ⊣ Is` with `α : I ≅ 𝟭` and `b : Is ⟶ 𝟭` related through the counit (so that `b` is the
conjugate of `α⁻¹`) and `b` monoidal, the projection comparison followed by `α ▷ N` is
`I (K ◁ b)` followed by `α`. -/
lemma projectionComparison_comp_whiskerRight_of_iso_id
    (hαb : ∀ W, α.inv.app (Is.obj W) ≫ bi.counit.app W = b W)
    (hb : ∀ X Y, δ Is X Y ≫ (b X ⊗ₘ b Y) = b (X ⊗ Y)) (K N : C) :
    bi.projectionComparison K N ≫ α.hom.app K ▷ N = I.map (K ◁ b N) ≫ α.hom.app (K ⊗ N) := by
  have hβ := conjugateIsoEquiv_id_hom_app bi α b hαb
  rw [projectionComparison_eq_of_iso bi Adjunction.id (conjugateIsoEquiv bi Adjunction.id α.symm)
      (μ_comp_hom_app_eq_of_δ _ (fun X Y ↦ by
        rw [hβ, hβ, hβ, id_δ, Category.comp_id]
        exact hb X Y)) K N,
    Equiv.symm_apply_apply, id_projectionComparison, hβ]
  have h := α.hom.naturality (K ◁ b N)
  simp only [Functor.id_map, Functor.id_obj] at h
  simp only [Iso.symm_inv, Iso.symm_hom, Functor.id_map, Category.id_comp, Category.assoc,
    ← comp_whiskerRight, Iso.inv_hom_id_app, Functor.id_obj, id_whiskerRight, Category.comp_id, h]

/-- **The exceptional projection morphism of the trivial compactification** `(𝟙, p)` of a proper
`p`, for abstract adjunctions: with `α : I ≅ 𝟭` and `b : Is ⟶ 𝟭` related through the counit of
`I ⊣ Is` and `b` monoidal, the composite of the projection morphism of `Ps ⊣ P`, the inverse
projection comparison of `I ⊣ Is` and `b`, followed by `P α`, is the projection morphism of
`Ps ⊣ P` read through `α`. -/
lemma trivialOpen_exceptionalProjection_comp {D : Type*} [Category D] [MonoidalCategory D]
    {Ps : D ⥤ C} {P : C ⥤ D} [Ps.OplaxMonoidal] (ap : Ps ⊣ P)
    (hαb : ∀ W, α.inv.app (Is.obj W) ≫ bi.counit.app W = b W)
    (hb : ∀ X Y, δ Is X Y ≫ (b X ⊗ₘ b Y) = b (X ⊗ Y)) (K : C) (B : D)
    [IsIso (bi.projectionComparison K (Ps.obj B))] :
    (ap.projectionMorphism (I.obj K) B ≫
        P.map (inv (bi.projectionComparison K (Ps.obj B)) ≫ I.map (K ◁ b (Ps.obj B)))) ≫
        P.map (α.hom.app (K ⊗ Ps.obj B)) =
      P.map (α.hom.app K) ▷ B ≫ ap.projectionMorphism K B := by
  have h := ap.projectionMorphism_natural_left (α.hom.app K) B
  simp only [Functor.id_obj] at h
  rw [h, Category.assoc, ← P.map_comp, Category.assoc,
    ← projectionComparison_comp_whiskerRight_of_iso_id bi α b hαb hb, IsIso.inv_hom_id_assoc]

end Trivial


section OfNatIsoRight

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G G' : C ⥤ D} [F.OplaxMonoidal] (adj : F ⊣ G) (e : G ≅ G')

omit [MonoidalCategory C] [MonoidalCategory D] [F.OplaxMonoidal] in
/-- The counit of `adj.ofNatIsoRight e` is `F e⁻¹` followed by the counit of `adj`. -/
lemma ofNatIsoRight_counit_app (A : C) :
    (adj.ofNatIsoRight e).counit.app A = F.map (e.inv.app A) ≫ adj.counit.app A := by
  rw [← homEquiv_symm_id, homEquiv_ofNatIsoRight_symm_apply, Category.id_comp,
    homEquiv_counit]

/-- The adjoint of a projection morphism along `F ⊣ G`: `F` of the projection morphism followed by
the counit is the comultiplication followed by the counit. -/
lemma map_projectionMorphism_comp_counit (A : C) (B : D) :
    F.map (adj.projectionMorphism A B) ≫ adj.counit.app (A ⊗ F.obj B) =
      δ F (G.obj A) B ≫ adj.counit.app A ▷ F.obj B :=
  map_homEquiv_comp_counit adj _

/-- A morphism `φ : G' A ⊗ B ⟶ G' (A ⊗ F B)` identified with the projection morphism of `F ⊣ G`
through `e : G ≅ G'` has the adjoint of a projection morphism along `adj.ofNatIsoRight e`:
`F φ` followed by the counit is the comultiplication followed by the counit. -/
lemma map_comp_ofNatIsoRight_counit {A : C} {B : D}
    (φ : G'.obj A ⊗ B ⟶ G'.obj (A ⊗ F.obj B))
    (hφ : φ ≫ e.inv.app _ = e.inv.app A ▷ B ≫ adj.projectionMorphism A B) :
    F.map φ ≫ (adj.ofNatIsoRight e).counit.app (A ⊗ F.obj B) =
      δ F (G'.obj A) B ≫ (adj.ofNatIsoRight e).counit.app A ▷ F.obj B := by
  rw [ofNatIsoRight_counit_app, ofNatIsoRight_counit_app, ← F.map_comp_assoc, hφ,
    F.map_comp_assoc, map_projectionMorphism_comp_counit, ← δ_natural_left_assoc,
    comp_whiskerRight]

end OfNatIsoRight

end CategoryTheory.Adjunction
