/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Right adjoints and Bousfield localizations of triangulated categories

Let `Φ : D' ⥤ D` be a triangulated functor between pretriangulated categories with a fully
faithful right adjoint `Ψ`, so that `D` is a Bousfield localization of `D'`. Let `F : D ⥤ T` be
a functor preserving zero morphisms. If `Φ ⋙ F` has a right adjoint `K`, then `F` has a right
adjoint, namely `Y ↦ Φ(K(Y))`
(`CategoryTheory.Functor.isLeftAdjoint_of_isLeftAdjoint_comp`).

The key point is that the objects `L = K(Y)` are local: the unit `η : L ⟶ ΨΦ(L)` is an
isomorphism. Indeed, let `L ⟶ ΨΦ(L) ⟶ N ⟶ L⟦1⟧` be a distinguished triangle. As `Φ(η)` is an
isomorphism, `Φ(N) = 0`, so that `Hom(N, ΨΦ(L)) = Hom(Φ(N), Φ(L)) = 0` and
`Hom(N⟦-1⟧, L) = Hom(FΦ(N⟦-1⟧), Y) = 0`, which forces `N = 0`.

This is the formal part of the proof of Stacks Tag 0F5Y (Stacks Lemma 19.15.1), where `Φ` is the
exact functor `D(R) ⥤ D(A)` given by the Gabriel-Popescu theorem; it is used in the blueprint
node `theorem-existence-exceptional-inverse-image--1`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Category

namespace CategoryTheory.Functor

/-- A functor `F : C ⥤ D` is a left adjoint as soon as for every `Y : D` there are an object
`G(Y)` and a morphism `u : F(G(Y)) ⟶ Y` such that `f ↦ F(f) ≫ u` is a bijection
`(W ⟶ G(Y)) ≃ (F(W) ⟶ Y)` for all `W`. -/
lemma isLeftAdjoint_of_bijective {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {G : D → C} (u : ∀ Y, F.obj (G Y) ⟶ Y)
    (hu : ∀ Y W, Function.Bijective (fun f : W ⟶ G Y ↦ F.map f ≫ u Y)) : F.IsLeftAdjoint := by
  let e : ∀ W Y, (F.obj W ⟶ Y) ≃ (W ⟶ G Y) := fun W Y ↦ (Equiv.ofBijective _ (hu Y W)).symm
  have he : ∀ W' W Y (f : W' ⟶ W) (g : F.obj W ⟶ Y), e W' Y (F.map f ≫ g) = f ≫ e W Y g := by
    intro W' W Y f g
    apply (Equiv.ofBijective _ (hu Y W')).injective
    have h₁ := (Equiv.ofBijective _ (hu Y W')).apply_symm_apply (F.map f ≫ g)
    have h₂ := (Equiv.ofBijective _ (hu Y W)).apply_symm_apply g
    simp only [Equiv.ofBijective_apply] at h₁ h₂
    simp only [e, Equiv.ofBijective_apply, F.map_comp, assoc, h₁, h₂]
  exact (Adjunction.adjunctionOfEquivRight e he).isLeftAdjoint

variable {D' D T : Type*} [Category* D'] [Category* D] [Category* T]
  [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D']
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [HasZeroMorphisms T]

/-- Let `Φ ⊣ Ψ` with `Ψ` fully faithful and `Φ` triangulated, and let `F : D ⥤ T` preserve zero
morphisms. If `Φ ⋙ F ⊣ K`, then the unit of `Φ ⊣ Ψ` is an isomorphism at `K(Y)`. -/
lemma isIso_unit_app_of_comp {Φ : D' ⥤ D} {Ψ : D ⥤ D'} (adj : Φ ⊣ Ψ) [Ψ.Full] [Ψ.Faithful]
    [Φ.CommShift ℤ] [Φ.IsTriangulated] (F : D ⥤ T) [F.PreservesZeroMorphisms] {K : T ⥤ D'}
    (adj' : Φ ⋙ F ⊣ K) (Y : T) : IsIso (adj.unit.app (K.obj Y)) := by
  let L := K.obj Y
  obtain ⟨N, p, q, hT⟩ := distinguished_cocone_triangle (adj.unit.app L)
  suffices hN : IsZero N from (Triangle.isZero₃_iff_isIso₁ _ hT).1 hN
  -- `Φ(N) = 0`
  have hΦN : IsZero (Φ.obj N) := by
    have h : Φ.map (adj.unit.app L) = CategoryTheory.inv (adj.counit.app (Φ.obj L)) := by
      rw [← cancel_mono (adj.counit.app (Φ.obj L)), IsIso.inv_hom_id]
      exact adj.left_triangle_components L
    have : IsIso (Φ.map (adj.unit.app L)) := by rw [h]; infer_instance
    exact Triangle.isZero₃_of_isIso₁ _ (Φ.map_distinguished _ hT) this
  -- `Hom(N, ΨΦ(L)) = 0`
  have h₁ : ∀ g : N ⟶ Ψ.obj (Φ.obj L), g = 0 := fun g ↦
    (adj.homEquiv _ _).symm.injective (hΦN.eq_of_src _ _)
  -- `Hom(N⟦-1⟧, L) = 0`
  have h₂ : ∀ g : N⟦(-1 : ℤ)⟧ ⟶ L, g = 0 := fun g ↦ by
    have : IsZero (F.obj (Φ.obj (N⟦(-1 : ℤ)⟧))) := F.map_isZero
      (IsZero.of_iso ((shiftFunctor D (-1 : ℤ)).map_isZero hΦN) ((Φ.commShiftIso (-1)).app N))
    exact (adj'.homEquiv _ _).symm.injective (this.eq_of_src _ _)
  -- hence `q = 0`
  have h₃ : q = 0 := by
    let adjs : shiftFunctor D' (-1 : ℤ) ⊣ shiftFunctor D' (1 : ℤ) :=
      (shiftEquiv' D' (-1 : ℤ) 1 (by norm_num)).toAdjunction
    apply (adjs.homEquiv N L).symm.injective
    rw [h₂ ((adjs.homEquiv N L).symm q)]
    simp [Adjunction.homEquiv_counit]
  have : 𝟙 N = 0 := by
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (rot_of_distTriang _ hT) (𝟙 N)
      (by simp [h₃])
    rw [hg, h₁ g, zero_comp]
  exact (IsZero.iff_id_eq_zero N).2 this

/-- **Right adjoints through a Bousfield localization** (formal part of Stacks Tag 0F5Y, via
Stacks Lemma 19.15.1; blueprint `theorem-existence-exceptional-inverse-image--1`): let `Φ : D' ⥤ D`
be a triangulated functor with a fully faithful right adjoint `Ψ`, and `F : D ⥤ T` a functor
preserving zero morphisms. If `Φ ⋙ F` is a left adjoint, then so is `F`. -/
theorem isLeftAdjoint_of_isLeftAdjoint_comp {Φ : D' ⥤ D} {Ψ : D ⥤ D'} (adj : Φ ⊣ Ψ) [Ψ.Full]
    [Ψ.Faithful] [Φ.CommShift ℤ] [Φ.IsTriangulated] (F : D ⥤ T) [F.PreservesZeroMorphisms]
    [(Φ ⋙ F).IsLeftAdjoint] : F.IsLeftAdjoint := by
  let adj' := Adjunction.ofIsLeftAdjoint (Φ ⋙ F)
  let K := (Φ ⋙ F).rightAdjoint
  have hη (Y : T) := isIso_unit_app_of_comp adj F adj' Y
  -- the candidate right adjoint `Y ↦ Φ(K(Y))`, with counit `u`
  let u (Y : T) : F.obj (Φ.obj (K.obj Y)) ⟶ Y := adj'.counit.app Y
  have hu (Y : T) (W : D) :
      Function.Bijective (fun f : W ⟶ Φ.obj (K.obj Y) ↦ F.map f ≫ u Y) := by
    have e : (fun f : W ⟶ Φ.obj (K.obj Y) ↦ F.map f ≫ u Y) =
        (fun g ↦ F.map (CategoryTheory.inv (adj.counit.app W)) ≫ g) ∘
          (adj'.homEquiv _ _).symm ∘
          (fun g ↦ g ≫ CategoryTheory.inv (adj.unit.app (K.obj Y))) ∘ (fun f ↦ Ψ.map f) := by
      ext f
      simp only [Function.comp_apply, Adjunction.homEquiv_counit, comp_map, u]
      rw [← F.map_comp_assoc]
      refine congrArg (fun g ↦ F.map g ≫ adj'.counit.app Y) ?_
      have h₁ : CategoryTheory.inv (adj.counit.app W) ≫ Φ.map (Ψ.map f) =
          f ≫ CategoryTheory.inv (adj.counit.app (Φ.obj (K.obj Y))) := by
        rw [IsIso.inv_comp_eq, ← assoc, IsIso.eq_comp_inv]
        exact adj.counit.naturality f
      have h₂ : CategoryTheory.inv (adj.counit.app (Φ.obj (K.obj Y))) =
          Φ.map (adj.unit.app (K.obj Y)) :=
        IsIso.inv_eq_of_inv_hom_id (adj.left_triangle_components _)
      rw [Φ.map_comp, ← assoc, h₁, h₂, assoc, ← Φ.map_comp, IsIso.hom_inv_id, Φ.map_id]
      exact (comp_id f).symm
    rw [e]
    have hΨ : Function.Bijective (fun f : W ⟶ Φ.obj (K.obj Y) ↦ Ψ.map f) :=
      (Functor.FullyFaithful.ofFullyFaithful Ψ).map_bijective _ _
    refine Function.Bijective.comp ?_ (Function.Bijective.comp (Equiv.bijective _)
      (Function.Bijective.comp ?_ hΨ))
    · exact ⟨fun a b h ↦ (cancel_epi _).1 h, fun g ↦ ⟨F.map (adj.counit.app W) ≫ g, by
        simp⟩⟩
    · exact ⟨fun a b h ↦ (cancel_mono _).1 h, fun g ↦ ⟨g ≫ adj.unit.app (K.obj Y), by simp⟩⟩
  exact isLeftAdjoint_of_bijective F u hu

end CategoryTheory.Functor
