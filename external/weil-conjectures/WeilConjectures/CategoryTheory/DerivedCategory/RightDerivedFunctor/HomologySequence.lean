/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The long exact sequence of a total right derived functor

Let `F : C ⥤ D` be an additive functor between abelian categories, `C` having K-injective
resolutions, and let `0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0` be a short exact sequence in `C`. Applying the
total right derived functor `RF` to the distinguished triangle `S₁ ⟶ S₂ ⟶ S₃ ⟶ S₁[1]` gives a
distinguished triangle in `D(D)`, whence a long exact sequence
`⋯ ⟶ Hⁿ(RF S₁) ⟶ Hⁿ(RF S₂) ⟶ Hⁿ(RF S₃) ⟶ Hⁿ⁺¹(RF S₁) ⟶ ⋯`
whose connecting maps are natural in morphisms of short exact sequences.

## Main results

- `CategoryTheory.Functor.rightDerivedHomologyδ`: the connecting morphism.
- `CategoryTheory.Functor.rightDerivedHomologySequence_exact₁`, `_exact₂`, `_exact₃`:
  exactness of the long exact sequence.
- `CategoryTheory.Functor.rightDerivedHomologyδ_naturality`: naturality of the connecting
  morphism.
-/

@[expose] public section

open CategoryTheory Limits Abelian Pretriangulated DerivedCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

variable {S : ShortComplex C} (hS : S.ShortExact)

/-- The distinguished triangle `RF S₁ ⟶ RF S₂ ⟶ RF S₃ ⟶ RF S₁[1]` attached to a short exact
sequence `S` of `C`. -/
noncomputable def rightDerivedSingleTriangle : Triangle (DerivedCategory D) :=
  F.rightDerivedFunctor.mapTriangle.obj hS.singleTriangle

lemma rightDerivedSingleTriangle_distinguished :
    F.rightDerivedSingleTriangle hS ∈ distTriang _ :=
  F.rightDerivedFunctor.map_distinguished _ hS.singleTriangle_distinguished

/-- The connecting morphism `Hⁿ⁰(RF S₃) ⟶ Hⁿ¹(RF S₁)`, `n₀ + 1 = n₁`, of the long exact sequence
of a short exact sequence `S`. -/
noncomputable def rightDerivedHomologyδ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor D n₀).obj (F.rightDerivedFunctor.obj ((singleFunctor C 0).obj S.X₃)) ⟶
      (homologyFunctor D n₁).obj (F.rightDerivedFunctor.obj ((singleFunctor C 0).obj S.X₁)) :=
  HomologySequence.δ (F.rightDerivedSingleTriangle hS) n₀ n₁ h

lemma rightDerivedHomology_map_comp_eq_zero (n : ℤ) :
    (homologyFunctor D n).map (F.rightDerivedFunctor.map ((singleFunctor C 0).map S.f)) ≫
      (homologyFunctor D n).map (F.rightDerivedFunctor.map ((singleFunctor C 0).map S.g)) =
        0 := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, S.zero, Functor.map_zero,
    Functor.map_zero, Functor.map_zero]

/-- **Exactness at `Hⁿ(RF S₂)`** of the long exact sequence of a short exact sequence. -/
lemma rightDerivedHomologySequence_exact₂ {S : ShortComplex C} (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk _ _ (F.rightDerivedHomology_map_comp_eq_zero (S := S) n)).Exact :=
  HomologySequence.exact₂ _ (F.rightDerivedSingleTriangle_distinguished hS) n

@[reassoc (attr := simp)]
lemma rightDerivedHomology_map_comp_δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor D n₀).map (F.rightDerivedFunctor.map ((singleFunctor C 0).map S.g)) ≫
      F.rightDerivedHomologyδ hS n₀ n₁ h = 0 :=
  HomologySequence.comp_δ _ (F.rightDerivedSingleTriangle_distinguished hS) n₀ n₁ h

@[reassoc (attr := simp)]
lemma rightDerivedHomologyδ_comp_map (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    F.rightDerivedHomologyδ hS n₀ n₁ h ≫
      (homologyFunctor D n₁).map (F.rightDerivedFunctor.map ((singleFunctor C 0).map S.f)) =
        0 :=
  HomologySequence.δ_comp _ (F.rightDerivedSingleTriangle_distinguished hS) n₀ n₁ h

/-- **Exactness at `Hⁿ⁰(RF S₃)`** of the long exact sequence of a short exact sequence. -/
lemma rightDerivedHomologySequence_exact₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _ (F.rightDerivedHomology_map_comp_δ hS n₀ n₁ h)).Exact :=
  HomologySequence.exact₃ _ (F.rightDerivedSingleTriangle_distinguished hS) n₀ n₁ h

/-- **Exactness at `Hⁿ¹(RF S₁)`** of the long exact sequence of a short exact sequence. -/
lemma rightDerivedHomologySequence_exact₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _ (F.rightDerivedHomologyδ_comp_map hS n₀ n₁ h)).Exact :=
  HomologySequence.exact₁ _ (F.rightDerivedSingleTriangle_distinguished hS) n₀ n₁ h

/-- **Naturality of the connecting morphism** in morphisms of short exact sequences. -/
@[reassoc]
lemma rightDerivedHomologyδ_naturality {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor D n₀).map (F.rightDerivedFunctor.map ((singleFunctor C 0).map φ.τ₃)) ≫
        F.rightDerivedHomologyδ h₂ n₀ n₁ h =
      F.rightDerivedHomologyδ h₁ n₀ n₁ h ≫
        (homologyFunctor D n₁).map (F.rightDerivedFunctor.map ((singleFunctor C 0).map φ.τ₁)) :=
  (homologyFunctor D 0).homologySequenceδ_naturality
    (F.rightDerivedFunctor.mapTriangle.map (ShortComplex.ShortExact.singleTriangle.map h₁ h₂ φ))
    n₀ n₁ h

end CategoryTheory.Functor
