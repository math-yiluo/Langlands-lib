/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap

/-!

# Projection morphisms of composite adjunctions

Let `R' ⊣ R` and `S' ⊣ S` be adjunctions with oplax monoidal left adjoints, and `Q' ⊣ Q` an
adjunction with `Q' ≅ S' ⋙ R'` compatibly with the oplax monoidal structures. Under the
identification `S R ≅ Q` of right adjoints, the projection morphism of `Q' ⊣ Q` at `(A, B)` is
the projection morphism of `S' ⊣ S` at `(R A, B)` followed by `S` applied to the projection
morphism of `R' ⊣ R` at `(A, S' B)` (`CategoryTheory.Adjunction.whiskerRight_projectionMorphism`).
In particular it is an isomorphism if these two are
(`CategoryTheory.Adjunction.isIso_projectionMorphism_of_comp`).

We also record that the invertibility of the projection morphism only depends on its first
argument up to isomorphism, and that it is equivalent to the invertibility of the left projection
morphism for left adjoints compatible with the braidings.

## Main statements

- `CategoryTheory.Adjunction.whiskerRight_projectionMorphism`: the projection morphism of a
  composite.
- `CategoryTheory.Adjunction.isIso_projectionMorphism_of_comp`: the projection morphism of a
  composite is an isomorphism if those of the factors are.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

section Single

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- The invertibility of the projection morphism `G A ⊗ B ⟶ G (A ⊗ F B)` only depends on `A` up
to isomorphism, by the naturality square (`projectionMorphism_natural_left`)
```
G A ⊗ B ──projection morphism──▶ G (A ⊗ F B)
   │ G φ ▷ B                        │ G (φ ▷ F B)
   ▼                                ▼
G A' ⊗ B ─projection morphism──▶ G (A' ⊗ F B)
```
whose vertical arrows are isomorphisms. -/
lemma isIso_projectionMorphism_iff_of_iso {A A' : C} (φ : A ≅ A') (B : D) :
    IsIso (adj.projectionMorphism A B) ↔ IsIso (adj.projectionMorphism A' B) := by
  have h := adj.projectionMorphism_natural_left φ.hom B
  constructor
  · intro
    rw [← isIso_comp_left_iff (G.map φ.hom ▷ B), h]
    infer_instance
  · intro
    rw [← isIso_comp_right_iff _ (G.map (φ.hom ▷ F.obj B)), ← h]
    infer_instance

variable [BraidedCategory C] [BraidedCategory D]

/-- For `F` compatible with the braidings, the projection morphism at `(A, B)` is an isomorphism
if the left projection morphism at `(B, A)` is, by the square (`leftProjectionMorphism_eq`)
```
B ⊗ G A ──left projection morphism──▶ G (F B ⊗ A)
   │ β                                   ▲ G β⁻¹
   ▼                                     │
G A ⊗ B ───projection morphism──────▶ G (A ⊗ F B)
```
whose vertical arrows are isomorphisms. -/
lemma isIso_projectionMorphism_of_isIso_leftProjectionMorphism
    (h : ∀ X Y : D, δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom = F.map (β_ X Y).hom ≫ δ F Y X)
    (A : C) (B : D) [IsIso (adj.leftProjectionMorphism B A)] :
    IsIso (adj.projectionMorphism A B) := by
  have : IsIso ((β_ B (G.obj A)).hom ≫ adj.projectionMorphism A B ≫
      G.map (β_ (F.obj B) A).inv) := by
    rw [← adj.leftProjectionMorphism_eq h]
    infer_instance
  rw [← isIso_comp_left_iff (β_ B (G.obj A)).hom, ← isIso_comp_right_iff _
    (G.map (β_ (F.obj B) A).inv), Category.assoc]
  infer_instance

end Single

section Composite

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]
  {R' : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} (adjR : R' ⊣ R)
  {S' : C₃ ⥤ C₂} {S : C₂ ⥤ C₃} (adjS : S' ⊣ S)
  {Q' : C₃ ⥤ C₁} {Q : C₁ ⥤ C₃} (adjQ : Q' ⊣ Q)
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃] [R'.OplaxMonoidal]
  [S'.OplaxMonoidal] [Q'.OplaxMonoidal]

/-- **The projection morphism of a composite.** Let `Q' ≅ S' ⋙ R'` be compatible with the oplax
monoidal structures and let `u : S R ≅ Q` be the identification of right adjoints. Then the
square
```
S R A ⊗ B ───────────u ▷ B────────────▶ Q A ⊗ B
   │ projection morphism of S             │ projection morphism of Q
   ▼                                      ▼
S (R A ⊗ S' B) ⟶ S R (A ⊗ R' S' B) ⟶ S R (A ⊗ Q' B) ──u──▶ Q (A ⊗ Q' B)
```
commutes, the lower row being made of `S` applied to the projection morphism of `R` and
`e⁻¹ : R' S' B ⟶ Q' B`. -/
lemma whiskerRight_projectionMorphism (e : Q' ≅ S' ⋙ R')
    (he : ∀ U V : C₃, δ Q' U V ≫ (e.hom.app U ⊗ₘ e.hom.app V) =
      e.hom.app (U ⊗ V) ≫ R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V))
    (A : C₁) (B : C₃) :
    (rightAdjointUniq ((adjS.comp adjR).ofNatIsoLeft e.symm) adjQ).hom.app A ▷ B ≫
        adjQ.projectionMorphism A B =
      adjS.projectionMorphism (R.obj A) B ≫
        S.map (adjR.projectionMorphism A (S'.obj B) ≫ R.map (A ◁ e.inv.app B)) ≫
        (rightAdjointUniq ((adjS.comp adjR).ofNatIsoLeft e.symm) adjQ).hom.app
          (A ⊗ Q'.obj B) := by
  set u := (rightAdjointUniq ((adjS.comp adjR).ofNatIsoLeft e.symm) adjQ).hom.app A
  have hc : e.inv.app (S.obj (R.obj A)) ≫ Q'.map u ≫ adjQ.counit.app A =
      R'.map (adjS.counit.app (R.obj A)) ≫ adjR.counit.app A := by
    rw [rightAdjointUniq_hom_app_counit, ofNatIsoLeft_counit]
    simp
  have hδ : e.inv.app (S.obj (R.obj A) ⊗ B) ≫ δ Q' (S.obj (R.obj A)) B =
      R'.map (δ S' _ B) ≫ δ R' (S'.obj (S.obj (R.obj A))) (S'.obj B) ≫
        (e.inv.app _ ⊗ₘ e.inv.app B) := by
    rw [← cancel_epi (e.hom.app _), Iso.hom_inv_id_app_assoc, ← reassoc_of% he,
      tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app, id_tensorHom_id,
      Category.comp_id]
  have key : e.inv.app (S.obj (R.obj A) ⊗ B) ≫ δ Q' (S.obj (R.obj A)) B ≫
      (Q'.map u ≫ adjQ.counit.app A) ▷ Q'.obj B =
      R'.map (δ S' (S.obj (R.obj A)) B ≫ adjS.counit.app (R.obj A) ▷ S'.obj B) ≫
        (δ R' (R.obj A) (S'.obj B) ≫ adjR.counit.app A ▷ R'.obj (S'.obj B)) ≫
        A ◁ e.inv.app B := by
    rw [reassoc_of% hδ, ← tensorHom_id, tensorHom_comp_tensorHom, Category.assoc, hc,
      Category.comp_id, Functor.map_comp, Category.assoc, tensorHom_def, comp_whiskerRight,
      Category.assoc, δ_natural_left_assoc]
    simp
  rw [projectionMorphism, ← homEquiv_naturality_left, ← δ_natural_left_assoc,
    ← comp_whiskerRight, homEquiv_eq_homEquiv_homEquiv adjR adjS adjQ e]
  erw [key]
  rw [homEquiv_naturality_left (adj := adjR), homEquiv_naturality_right (adj := adjR),
    homEquiv_naturality_right (adj := adjS)]
  simp only [Category.assoc]
  rfl

/-- **The projection morphism of a composite is an isomorphism** if the projection morphisms of
`S' ⊣ S` at `(R A, B)` and of `R' ⊣ R` at `(A, S' B)` are (`whiskerRight_projectionMorphism`). -/
lemma isIso_projectionMorphism_of_comp (e : Q' ≅ S' ⋙ R')
    (he : ∀ U V : C₃, δ Q' U V ≫ (e.hom.app U ⊗ₘ e.hom.app V) =
      e.hom.app (U ⊗ V) ≫ R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V))
    (A : C₁) (B : C₃) [IsIso (adjS.projectionMorphism (R.obj A) B)]
    [IsIso (adjR.projectionMorphism A (S'.obj B))] :
    IsIso (adjQ.projectionMorphism A B) := by
  rw [← isIso_comp_left_iff
    ((rightAdjointUniq ((adjS.comp adjR).ofNatIsoLeft e.symm) adjQ).hom.app A ▷ B),
    whiskerRight_projectionMorphism adjR adjS adjQ e he]
  infer_instance

end Composite

end CategoryTheory.Adjunction
