/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal

/-!
# Tensor comparisons of left derived functors along comparisons of counits

Let `G₁ : C ⥤ D'`, `G₂ : D' ⥤ E` and `H : C ⥤ E` be strong monoidal functors whose left derived
functors carry tensor comparisons (`CategoryTheory.Functor.leftDerivedTensorComparison`); the
functors need not be exact. Let `β : LG₁ ⋙ LG₂ ⟶ LH` be a natural transformation which, through
the counits of the left derived functors, is given on every complex `X` by a morphism
`t X : G₂(G₁ X) ⟶ H X` of the homotopy category, the morphisms `t` being compatible with the
comonoidal structures. Then `β` carries the composite of the tensor comparisons of `LG₁` and `LG₂`
to the tensor comparison of `LH`
(`CategoryTheory.Functor.map_leftDerivedTensorComparison_comp_tensorHom_of_counit`).

As a consequence, an isomorphism `LG₁ ⋙ LG₂ ≅ LF₁ ⋙ LF₂` compatible through the counits with a
monoidal isomorphism of the underived composites identifies the composites of the tensor
comparisons (`CategoryTheory.Functor.map_leftDerivedTensorComparison_comp_eq_of_counit`). This
generalizes `CategoryTheory.Functor.map_leftDerivedTensorComparison_comp_eq_of_iso` to functors
which are not exact: no composition isomorphism of left derived functors is needed, only a
comparison `LF₁ ⋙ LF₂ ⟶ LH` with the left derived functor of some functor `H`.
-/

@[expose] public section

universe u u₁ u₂ u₃ u₄

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

open OplaxMonoidal LaxMonoidal

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  {D' : Type u₃} [Category.{u + 1} D'] [Abelian D'] [IsGrothendieckAbelian.{u + 1} D']
  [MonoidalCategory D'] [MonoidalPreadditive D'] [MonoidalClosed D'] [BraidedCategory D']
  [HasFunctorialFlatResolution D']
  {E : Type u₄} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
  [HasFunctorialFlatResolution E]

/-- The naturality of the tensor comparison of `LF`, with tensor products of morphisms, for a
functor `F` which need not be exact. -/
@[reassoc]
lemma leftDerivedTensorComparison_app_app_naturality (F : C ⥤ D) [F.Additive]
    [F.PreservesKFlatQuasiIso] [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
    {K₁ K₂ M₁ M₂ : DerivedCategory C} (f : K₁ ⟶ K₂) (g : M₁ ⟶ M₂) :
    F.leftDerivedFunctor.map (f ⊗ₘ g) ≫ (F.leftDerivedTensorComparison.app K₂).app M₂ =
      (F.leftDerivedTensorComparison.app K₁).app M₁ ≫
        (F.leftDerivedFunctor.map f ⊗ₘ F.leftDerivedFunctor.map g) := by
  have h₁ := congr_app (F.leftDerivedTensorComparison.naturality f) M₁
  have h₂ := (F.leftDerivedTensorComparison.app K₂).naturality g
  dsimp at h₁ h₂
  rw [tensorHom_def, Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁, tensorHom_def]

/-- Let `β : LG₁ ⋙ LG₂ ⟶ LH` be given through the counits of the left derived functors by
morphisms `t X : G₂(G₁ X) ⟶ H X` of the homotopy category compatible with the comonoidal
structures. Then `β` carries the composite of the tensor comparisons of `LG₁` and `LG₂` to the
tensor comparison of `LH`:
```
LG₂(LG₁(K ⊗ᴸ M)) ⟶ LG₂(LG₁K ⊗ᴸ LG₁M) ⟶ LG₂LG₁K ⊗ᴸ LG₂LG₁M ⟶ LH K ⊗ᴸ LH M
```
is `β` followed by the tensor comparison of `LH`. -/
@[reassoc]
lemma map_leftDerivedTensorComparison_comp_tensorHom_of_counit
    (G₁ : C ⥤ D') [G₁.Additive] [G₁.PreservesKFlatQuasiIso] [G₁.PreservesFlat]
    [G₁.IsLeftAdjoint] [G₁.Monoidal]
    (G₂ : D' ⥤ E) [G₂.Additive] [G₂.PreservesKFlatQuasiIso] [G₂.PreservesFlat]
    [G₂.IsLeftAdjoint] [G₂.Monoidal]
    (H : C ⥤ E) [H.Additive] [H.PreservesKFlatQuasiIso] [H.PreservesFlat]
    [H.IsLeftAdjoint] [H.Monoidal]
    (β : G₁.leftDerivedFunctor ⋙ G₂.leftDerivedFunctor ⟶ H.leftDerivedFunctor)
    (t : ∀ X : HomotopyCategory C (.up ℤ), (G₂.mapHomotopyCategory (.up ℤ)).obj
      ((G₁.mapHomotopyCategory (.up ℤ)).obj X) ⟶ (H.mapHomotopyCategory (.up ℤ)).obj X)
    (hβ : ∀ X, β.app (Qh.obj X) ≫ H.leftDerivedFunctorCounit.app X =
      G₂.leftDerivedFunctor.map (G₁.leftDerivedFunctorCounit.app X) ≫
        G₂.leftDerivedFunctorCounit.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) ≫ Qh.map (t X))
    (ht : ∀ X₁ X₂, t (X₁ ⊗ X₂) ≫ ((mapHomotopyCategoryδNatTrans (.up ℤ) H).app X₁).app X₂ =
      (G₂.mapHomotopyCategory (.up ℤ)).map
          (((mapHomotopyCategoryδNatTrans (.up ℤ) G₁).app X₁).app X₂) ≫
        ((mapHomotopyCategoryδNatTrans (.up ℤ) G₂).app
          ((G₁.mapHomotopyCategory (.up ℤ)).obj X₁)).app
            ((G₁.mapHomotopyCategory (.up ℤ)).obj X₂) ≫ (t X₁ ⊗ₘ t X₂))
    (K M : DerivedCategory C) :
    G₂.leftDerivedFunctor.map ((G₁.leftDerivedTensorComparison.app K).app M) ≫
        (G₂.leftDerivedTensorComparison.app (G₁.leftDerivedFunctor.obj K)).app
          (G₁.leftDerivedFunctor.obj M) ≫ (β.app K ⊗ₘ β.app M) =
      β.app (K ⊗ M) ≫ (H.leftDerivedTensorComparison.app K).app M := by
  have h := leftDerived₂_ext (derivedTensorLeftDerived H) (derivedTensorLeftDerivedCounit H)
    (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
    ((postcompose₂.obj (G₁.leftDerivedFunctor ⋙ G₂.leftDerivedFunctor)).obj (curriedTensor _))
    ((postcompose₂.obj G₂.leftDerivedFunctor).map G₁.leftDerivedTensorComparison ≫
      (((whiskeringLeft₂ _).obj G₁.leftDerivedFunctor).obj G₁.leftDerivedFunctor).map
        G₂.leftDerivedTensorComparison ≫
      (((whiskeringLeft₂ _).map β).app
        (G₁.leftDerivedFunctor ⋙ G₂.leftDerivedFunctor)).app (curriedTensor _) ≫
      (((whiskeringLeft₂ _).obj H.leftDerivedFunctor).map β).app (curriedTensor _))
    ((postcompose₂.map β).app (curriedTensor _) ≫ H.leftDerivedTensorComparison) (by
      ext X₁ X₂
      dsimp
      simp only [Category.assoc]
      have cG₁ := congrArg G₂.leftDerivedFunctor.map
        (leftDerivedTensorComparison_app_app_comp_tensorHom G₁ X₁ X₂)
      have nG := G₂.leftDerivedFunctorCounit.naturality
        (X := (G₁.mapHomotopyCategory (.up ℤ)).obj (X₁ ⊗ X₂))
        (Y := (G₁.mapHomotopyCategory (.up ℤ)).obj X₁ ⊗
          (G₁.mapHomotopyCategory (.up ℤ)).obj X₂)
        (((mapHomotopyCategoryδNatTrans (.up ℤ) G₁).app X₁).app X₂)
      have nβ := β.naturality (μ Qh X₁ X₂)
      simp only [Functor.map_comp] at cG₁
      dsimp only [Functor.comp_obj, Functor.comp_map] at nG nβ
      rw [derivedTensorLeftDerivedCounit_app_app, ← tensorHom_def_assoc,
        tensorHom_comp_tensorHom_assoc, hβ, hβ, ← tensorHom_comp_tensorHom_assoc,
        ← tensorHom_comp_tensorHom_assoc, μ_natural,
        ← leftDerivedTensorComparison_app_app_naturality_assoc]
      erw [leftDerivedTensorComparison_app_app_comp_tensorHom_assoc G₂
        ((G₁.mapHomotopyCategory _).obj X₁) ((G₁.mapHomotopyCategory _).obj X₂)]
      rw [reassoc_of% cG₁,
        reassoc_of% nG, leftDerivedTensorComparison_app_app_comp_tensorHom,
        ← reassoc_of% nβ, reassoc_of% (hβ (X₁ ⊗ X₂)), ← Qh.map_comp, ← Qh.map_comp,
        ← Qh.map_comp, ht])
  have h' := congr_app (congr_app h K) M
  dsimp at h'
  rw [tensorHom_def, h']

/-- Let `α : LG₁ ⋙ LG₂ ≅ LF₁ ⋙ LF₂` be given through the counits of the left derived functors by
morphisms `t X : G₂(G₁ X) ⟶ F₂(F₁ X)` of the homotopy category compatible with the comonoidal
structures (for instance by a monoidal isomorphism `G₁ ⋙ G₂ ≅ F₁ ⋙ F₂`), and let
`β : LF₁ ⋙ LF₂ ⟶ LH` be an isomorphism given through the counits by morphisms
`s X : F₂(F₁ X) ⟶ H X` compatible with the comonoidal structures (for instance `H = F₁ ⋙ F₂`
and `s = 𝟙`). Then `α` identifies the composite of the tensor comparisons of `LF₁` and `LF₂`
with the composite of those of `LG₁` and `LG₂`:
```
LF₂(LF₁(K ⊗ᴸ M)) ⟶ LF₂(LF₁K ⊗ᴸ LF₁M) ⟶ LF₂LF₁K ⊗ᴸ LF₂LF₁M
```
is `α⁻¹` followed by the corresponding composite for `G₁, G₂` and by `α ⊗ α`. The functors need
not be exact. -/
lemma map_leftDerivedTensorComparison_comp_eq_of_counit
    (F₁ : C ⥤ D) [F₁.Additive] [F₁.PreservesKFlatQuasiIso] [F₁.PreservesFlat]
    [F₁.IsLeftAdjoint] [F₁.Monoidal]
    (F₂ : D ⥤ E) [F₂.Additive] [F₂.PreservesKFlatQuasiIso] [F₂.PreservesFlat]
    [F₂.IsLeftAdjoint] [F₂.Monoidal]
    (G₁ : C ⥤ D') [G₁.Additive] [G₁.PreservesKFlatQuasiIso] [G₁.PreservesFlat]
    [G₁.IsLeftAdjoint] [G₁.Monoidal]
    (G₂ : D' ⥤ E) [G₂.Additive] [G₂.PreservesKFlatQuasiIso] [G₂.PreservesFlat]
    [G₂.IsLeftAdjoint] [G₂.Monoidal]
    (H : C ⥤ E) [H.Additive] [H.PreservesKFlatQuasiIso] [H.PreservesFlat]
    [H.IsLeftAdjoint] [H.Monoidal]
    (α : G₁.leftDerivedFunctor ⋙ G₂.leftDerivedFunctor ≅
      F₁.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor)
    (β : F₁.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor ⟶ H.leftDerivedFunctor) [IsIso β]
    (t : ∀ X : HomotopyCategory C (.up ℤ), (G₂.mapHomotopyCategory (.up ℤ)).obj
      ((G₁.mapHomotopyCategory (.up ℤ)).obj X) ⟶
        (F₂.mapHomotopyCategory (.up ℤ)).obj ((F₁.mapHomotopyCategory (.up ℤ)).obj X))
    (s : ∀ X : HomotopyCategory C (.up ℤ), (F₂.mapHomotopyCategory (.up ℤ)).obj
      ((F₁.mapHomotopyCategory (.up ℤ)).obj X) ⟶ (H.mapHomotopyCategory (.up ℤ)).obj X)
    (hα : ∀ X, α.hom.app (Qh.obj X) ≫
        F₂.leftDerivedFunctor.map (F₁.leftDerivedFunctorCounit.app X) ≫
          F₂.leftDerivedFunctorCounit.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) =
      G₂.leftDerivedFunctor.map (G₁.leftDerivedFunctorCounit.app X) ≫
        G₂.leftDerivedFunctorCounit.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) ≫ Qh.map (t X))
    (ht : ∀ X₁ X₂, t (X₁ ⊗ X₂) ≫ (F₂.mapHomotopyCategory (.up ℤ)).map
          (((mapHomotopyCategoryδNatTrans (.up ℤ) F₁).app X₁).app X₂) ≫
        ((mapHomotopyCategoryδNatTrans (.up ℤ) F₂).app
          ((F₁.mapHomotopyCategory (.up ℤ)).obj X₁)).app
            ((F₁.mapHomotopyCategory (.up ℤ)).obj X₂) =
      (G₂.mapHomotopyCategory (.up ℤ)).map
          (((mapHomotopyCategoryδNatTrans (.up ℤ) G₁).app X₁).app X₂) ≫
        ((mapHomotopyCategoryδNatTrans (.up ℤ) G₂).app
          ((G₁.mapHomotopyCategory (.up ℤ)).obj X₁)).app
            ((G₁.mapHomotopyCategory (.up ℤ)).obj X₂) ≫ (t X₁ ⊗ₘ t X₂))
    (hβ : ∀ X, β.app (Qh.obj X) ≫ H.leftDerivedFunctorCounit.app X =
      F₂.leftDerivedFunctor.map (F₁.leftDerivedFunctorCounit.app X) ≫
        F₂.leftDerivedFunctorCounit.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) ≫ Qh.map (s X))
    (hs : ∀ X₁ X₂, s (X₁ ⊗ X₂) ≫ ((mapHomotopyCategoryδNatTrans (.up ℤ) H).app X₁).app X₂ =
      (F₂.mapHomotopyCategory (.up ℤ)).map
          (((mapHomotopyCategoryδNatTrans (.up ℤ) F₁).app X₁).app X₂) ≫
        ((mapHomotopyCategoryδNatTrans (.up ℤ) F₂).app
          ((F₁.mapHomotopyCategory (.up ℤ)).obj X₁)).app
            ((F₁.mapHomotopyCategory (.up ℤ)).obj X₂) ≫ (s X₁ ⊗ₘ s X₂))
    (K M : DerivedCategory C) :
    F₂.leftDerivedFunctor.map ((F₁.leftDerivedTensorComparison.app K).app M) ≫
        (F₂.leftDerivedTensorComparison.app (F₁.leftDerivedFunctor.obj K)).app
          (F₁.leftDerivedFunctor.obj M) =
      α.inv.app (K ⊗ M) ≫
        G₂.leftDerivedFunctor.map ((G₁.leftDerivedTensorComparison.app K).app M) ≫
        (G₂.leftDerivedTensorComparison.app (G₁.leftDerivedFunctor.obj K)).app
          (G₁.leftDerivedFunctor.obj M) ≫ (α.hom.app K ⊗ₘ α.hom.app M) := by
  have hG := map_leftDerivedTensorComparison_comp_tensorHom_of_counit G₁ G₂ H (α.hom ≫ β)
    (fun X ↦ t X ≫ s X)
    (fun X ↦ by
      rw [NatTrans.comp_app, Category.assoc, hβ, reassoc_of% (hα X), Qh.map_comp])
    (fun X₁ X₂ ↦ by
      rw [Category.assoc, hs, reassoc_of% (ht X₁ X₂), tensorHom_comp_tensorHom])
    K M
  rw [← cancel_mono (β.app K ⊗ₘ β.app M), Category.assoc,
    map_leftDerivedTensorComparison_comp_tensorHom_of_counit F₁ F₂ H β s hβ hs]
  simp only [Category.assoc, tensorHom_comp_tensorHom]
  simp only [NatTrans.comp_app] at hG
  rw [hG, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The special case of `CategoryTheory.Functor.map_leftDerivedTensorComparison_comp_eq_of_counit`
for a monoidal isomorphism `τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂`: let `α : LG₁ ⋙ LG₂ ≅ LF₁ ⋙ LF₂` be given
through the counits of the left derived functors by `τ`, and let
`β : LF₁ ⋙ LF₂ ⟶ L(F₁ ⋙ F₂)` be an isomorphism compatible with the counits. Then `α` identifies
the composite of the tensor comparisons of `LF₁` and `LF₂` with the composite of those of `LG₁`
and `LG₂`. The functors need not be exact. -/
lemma map_leftDerivedTensorComparison_comp_eq_of_counit_of_iso
    (F₁ : C ⥤ D) [F₁.Additive] [F₁.PreservesKFlatQuasiIso] [F₁.PreservesFlat]
    [F₁.IsLeftAdjoint] [F₁.Monoidal]
    (F₂ : D ⥤ E) [F₂.Additive] [F₂.PreservesKFlatQuasiIso] [F₂.PreservesFlat]
    [F₂.IsLeftAdjoint] [F₂.Monoidal]
    (G₁ : C ⥤ D') [G₁.Additive] [G₁.PreservesKFlatQuasiIso] [G₁.PreservesFlat]
    [G₁.IsLeftAdjoint] [G₁.Monoidal]
    (G₂ : D' ⥤ E) [G₂.Additive] [G₂.PreservesKFlatQuasiIso] [G₂.PreservesFlat]
    [G₂.IsLeftAdjoint] [G₂.Monoidal] [(F₁ ⋙ F₂).PreservesKFlatQuasiIso]
    (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) [NatTrans.IsMonoidal τ.hom]
    (α : G₁.leftDerivedFunctor ⋙ G₂.leftDerivedFunctor ≅
      F₁.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor)
    (β : F₁.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor ⟶ (F₁ ⋙ F₂).leftDerivedFunctor)
    [IsIso β]
    (hα : ∀ X, α.hom.app (Qh.obj X) ≫
        F₂.leftDerivedFunctor.map (F₁.leftDerivedFunctorCounit.app X) ≫
          F₂.leftDerivedFunctorCounit.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) =
      G₂.leftDerivedFunctor.map (G₁.leftDerivedFunctorCounit.app X) ≫
        G₂.leftDerivedFunctorCounit.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
          Qh.map ((NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app X))
    (hβ : ∀ X, β.app (Qh.obj X) ≫ (F₁ ⋙ F₂).leftDerivedFunctorCounit.app X =
      F₂.leftDerivedFunctor.map (F₁.leftDerivedFunctorCounit.app X) ≫
        F₂.leftDerivedFunctorCounit.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
          Qh.map ((mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app X))
    (K M : DerivedCategory C) :
    F₂.leftDerivedFunctor.map ((F₁.leftDerivedTensorComparison.app K).app M) ≫
        (F₂.leftDerivedTensorComparison.app (F₁.leftDerivedFunctor.obj K)).app
          (F₁.leftDerivedFunctor.obj M) =
      α.inv.app (K ⊗ M) ≫
        G₂.leftDerivedFunctor.map ((G₁.leftDerivedTensorComparison.app K).app M) ≫
        (G₂.leftDerivedTensorComparison.app (G₁.leftDerivedFunctor.obj K)).app
          (G₁.leftDerivedFunctor.obj M) ≫ (α.hom.app K ⊗ₘ α.hom.app M) :=
  map_leftDerivedTensorComparison_comp_eq_of_counit F₁ F₂ G₁ G₂ (F₁ ⋙ F₂) α β
    (fun X ↦ (NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app X)
    (fun X ↦ (mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app X) hα
    (fun X₁ X₂ ↦ by
      rw [← mapHomotopyCategoryδNatTrans_comp,
        ← reassoc_of% (mapHomotopyCategoryδNatTrans_comp G₁ G₂ X₁ X₂)]
      exact mapHomotopyCategoryδNatTrans_naturality τ.hom X₁ X₂)
    hβ
    (fun X₁ X₂ ↦ by
      simp only [mapHomotopyCategoryCompIso_refl_hom_app]
      erw [Category.id_comp, id_tensorHom_id, Category.comp_id]
      exact mapHomotopyCategoryδNatTrans_comp F₁ F₂ X₁ X₂)
    K M

end CategoryTheory.Functor
