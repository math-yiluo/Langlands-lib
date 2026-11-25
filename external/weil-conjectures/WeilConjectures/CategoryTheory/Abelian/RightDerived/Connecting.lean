/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence

/-!
# The connecting morphism of right derived functors, naturally

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has injective
resolutions. For a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `C` we define the connecting
morphism `δ : R^q F C ⟶ R^{q+1} F A` of the long exact sequence of right derived functors
(`CategoryTheory.ShortComplex.ShortExact.rightDerivedδ`), prove the exactness of the long exact
sequence at `R^q F C` and at `R^{q + 1} F A`, and prove that `δ` is natural in the short exact
sequence.

As in `CategoryTheory.ShortComplex.ShortExact.exists_rightDerived_δ_exact`, the connecting
morphism comes from the distinguished triangle `A[0] ⟶ B[0] ⟶ C[0] ⟶ A[0][1]` in the bounded
below derived category, to which the triangulated functor `R⁺F` is applied; it is natural since
a morphism of short exact sequences induces a morphism of these triangles.

## Main definitions

- `CategoryTheory.ShortComplex.ShortExact.rightDerivedδ`: the connecting morphism.

## Main statements

- `CategoryTheory.ShortComplex.ShortExact.rightDerivedδ_naturality`: its naturality.
- `CategoryTheory.ShortComplex.ShortExact.rightDerivedδ_exact₂`,
  `CategoryTheory.ShortComplex.ShortExact.rightDerivedδ_exact₃`: the exactness of the long exact
  sequence at `R^q F C` and at `R^{q + 1} F A`.
-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

namespace ShortComplex.ShortExact

section Triangle

variable [HasDerivedCategory C] {S : ShortComplex C} (hS : S.ShortExact)

/-- The triangle `A[0] ⟶ B[0] ⟶ C[0] ⟶ A[0][1]` of `DerivedCategory.Plus C` attached to a short
exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`. -/
noncomputable def plusSingleTriangle : Triangle (DerivedCategory.Plus C) :=
  Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map S.f)
    ((DerivedCategory.Plus.singleFunctor C 0).map S.g)
    (DerivedCategory.Plus.ι.preimage
      ((DerivedCategory.Plus.singleFunctorιIso C 0).hom.app S.X₃ ≫ hS.singleδ ≫
        ((DerivedCategory.Plus.singleFunctorιIso C 0).inv.app S.X₁)⟦(1 : ℤ)⟧' ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app _))

lemma ι_map_plusSingleTriangle_mor₃ :
    DerivedCategory.Plus.ι.map hS.plusSingleTriangle.mor₃ =
      (DerivedCategory.Plus.singleFunctorιIso C 0).hom.app S.X₃ ≫ hS.singleδ ≫
        ((DerivedCategory.Plus.singleFunctorιIso C 0).inv.app S.X₁)⟦(1 : ℤ)⟧' ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app _ :=
  Functor.map_preimage _ _

lemma plusSingleTriangle_distinguished : hS.plusSingleTriangle ∈ distTriang _ := by
  let i := DerivedCategory.Plus.singleFunctorιIso C 0
  rw [← DerivedCategory.Plus.ι.map_distinguished_iff]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _ ?_
  refine Triangle.isoMk _ _ (i.app S.X₁) (i.app S.X₂) (i.app S.X₃) ?_ ?_ ?_
  · exact i.hom.naturality S.f
  · exact i.hom.naturality S.g
  · change (DerivedCategory.Plus.ι.map hS.plusSingleTriangle.mor₃ ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app _) ≫
        (i.hom.app S.X₁)⟦(1 : ℤ)⟧' = i.hom.app S.X₃ ≫ hS.singleδ
    rw [ι_map_plusSingleTriangle_mor₃]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id,
      Category.comp_id]

variable {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)

/-- A morphism of short exact sequences induces a morphism of the attached triangles of
`DerivedCategory.Plus C`. -/
noncomputable def plusSingleTriangleMap : h₁.plusSingleTriangle ⟶ h₂.plusSingleTriangle where
  hom₁ := (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁
  hom₂ := (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₂
  hom₃ := (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃
  comm₁ := by
    simp only [plusSingleTriangle, Triangle.mk_mor₁, ← Functor.map_comp, φ.comm₁₂]
  comm₂ := by
    simp only [plusSingleTriangle, Triangle.mk_mor₂, ← Functor.map_comp, φ.comm₂₃]
  comm₃ := by
    apply DerivedCategory.Plus.ι.map_injective
    have h := (singleTriangle.map h₁ h₂ φ).comm₃
    simp only [singleTriangle_mor₃, singleTriangle.map_hom₁, singleTriangle.map_hom₃] at h
    rw [Functor.map_comp, Functor.map_comp, ι_map_plusSingleTriangle_mor₃,
      ι_map_plusSingleTriangle_mor₃]
    simp only [Category.assoc, ← Functor.commShiftIso_inv_naturality]
    have e₁ := (DerivedCategory.Plus.singleFunctorιIso C 0).hom.naturality φ.τ₁
    have e₃ := (DerivedCategory.Plus.singleFunctorιIso C 0).hom.naturality φ.τ₃
    simp only [Functor.comp_map] at e₁ e₃
    simp only [DerivedCategory.Plus.singleFunctorιIso, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Category.id_comp, Category.comp_id] at e₁ e₃ ⊢
    rw [e₁, e₃]
    erw [Category.id_comp, Functor.map_id, Category.id_comp, Functor.map_id, Category.id_comp]
    rw [reassoc_of% h]
    rfl

end Triangle

section Delta

variable (F : C ⥤ D) [F.Additive] [EnoughInjectives C] [HasDerivedCategory C]
  [HasDerivedCategory D] {S : ShortComplex C} (hS : S.ShortExact)

/-- The image under `R⁺F`, in the derived category of `D`, of the triangle
`A[0] ⟶ B[0] ⟶ C[0] ⟶ A[0][1]` attached to a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`. -/
noncomputable abbrev rightDerivedTriangle : Triangle (DerivedCategory D) :=
  (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj hS.plusSingleTriangle

lemma rightDerivedTriangle_distinguished : hS.rightDerivedTriangle F ∈ distTriang _ :=
  Functor.map_distinguished _ _ hS.plusSingleTriangle_distinguished

variable [HasInjectiveResolutions C]

/-- The connecting morphism `R^q F C ⟶ R^{q + 1} F A` of the long exact sequence of right derived
functors attached to a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`: the connecting morphism of the
homology long exact sequence of the image under `R⁺F` of the distinguished triangle
`A[0] ⟶ B[0] ⟶ C[0] ⟶ A[0][1]`. -/
noncomputable def rightDerivedδ (q : ℕ) :
    (F.rightDerived q).obj S.X₃ ⟶ (F.rightDerived (q + 1)).obj S.X₁ :=
  (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).inv.app S.X₃ ≫
    DerivedCategory.HomologySequence.δ (hS.rightDerivedTriangle F) q _ (Nat.cast_succ q).symm ≫
      (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso (q + 1)).hom.app S.X₁

@[reassoc (attr := simp)]
lemma comp_rightDerivedδ (q : ℕ) : (F.rightDerived q).map S.g ≫ hS.rightDerivedδ F q = 0 := by
  let e := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
  refine ((e q).inv.naturality_assoc S.g _).trans ?_
  refine (congrArg ((e q).inv.app S.X₂ ≫ ·)
    (DerivedCategory.HomologySequence.comp_δ_assoc _ (hS.rightDerivedTriangle_distinguished F)
      q _ (Nat.cast_succ q).symm _)).trans ?_
  erw [zero_comp, comp_zero]

@[reassoc (attr := simp)]
lemma rightDerivedδ_comp (q : ℕ) :
    hS.rightDerivedδ F q ≫ (F.rightDerived (q + 1)).map S.f = 0 := by
  let e := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
  simp only [rightDerivedδ, Category.assoc]
  refine (congrArg (fun x ↦ (e q).inv.app S.X₃ ≫
    DerivedCategory.HomologySequence.δ (hS.rightDerivedTriangle F) q _ (Nat.cast_succ q).symm ≫ x)
    ((e (q + 1)).hom.naturality S.f).symm).trans ?_
  refine (congrArg ((e q).inv.app S.X₃ ≫ ·)
    (DerivedCategory.HomologySequence.δ_comp_assoc _ (hS.rightDerivedTriangle_distinguished F)
      q _ (Nat.cast_succ q).symm _)).trans ?_
  erw [zero_comp, comp_zero]

/-- The long exact sequence of right derived functors is exact at `R^q F C`. -/
lemma rightDerivedδ_exact₂ (q : ℕ) :
    (ShortComplex.mk ((F.rightDerived q).map S.g) (hS.rightDerivedδ F q)
      (hS.comp_rightDerivedδ F q)).Exact := by
  let e := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (DerivedCategory.HomologySequence.exact₃ _ (hS.rightDerivedTriangle_distinguished F) q _
      (Nat.cast_succ q).symm)
  exact ShortComplex.isoMk ((e q).app S.X₂) ((e q).app S.X₃) ((e (q + 1)).app S.X₁)
    ((e q).hom.naturality S.g).symm (Iso.hom_inv_id_app_assoc (e q) S.X₃ _)

/-- The long exact sequence of right derived functors is exact at `R^{q + 1} F A`. -/
lemma rightDerivedδ_exact₃ (q : ℕ) :
    (ShortComplex.mk (hS.rightDerivedδ F q) ((F.rightDerived (q + 1)).map S.f)
      (hS.rightDerivedδ_comp F q)).Exact := by
  let e := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (DerivedCategory.HomologySequence.exact₁ _ (hS.rightDerivedTriangle_distinguished F) q _
      (Nat.cast_succ q).symm)
  exact ShortComplex.isoMk ((e q).app S.X₃) ((e (q + 1)).app S.X₁) ((e (q + 1)).app S.X₂)
    (Iso.hom_inv_id_app_assoc (e q) S.X₃ _) ((e (q + 1)).hom.naturality S.f).symm

variable {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)

/-- **The connecting morphism is natural** in the short exact sequence. -/
@[reassoc]
lemma rightDerivedδ_naturality (q : ℕ) :
    h₁.rightDerivedδ F q ≫ (F.rightDerived (q + 1)).map φ.τ₁ =
      (F.rightDerived q).map φ.τ₃ ≫ h₂.rightDerivedδ F q := by
  let e := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
  let ψ := (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.map
    (plusSingleTriangleMap h₁ h₂ φ)
  have hδ := (DerivedCategory.homologyFunctor D 0).homologySequenceδ_naturality ψ q _
    (Nat.cast_succ q).symm
  simp only [rightDerivedδ, Category.assoc]
  rw [← (e (q + 1)).hom.naturality φ.τ₁, (e q).inv.naturality_assoc φ.τ₃]
  congr 1
  simp only [← Category.assoc]
  congr 1
  exact hδ.symm

end Delta

end ShortComplex.ShortExact

end CategoryTheory
