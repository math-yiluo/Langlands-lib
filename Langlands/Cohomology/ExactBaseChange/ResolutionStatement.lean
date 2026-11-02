import Langlands.Cohomology.ExactBaseChange
import Langlands.Cohomology.AcyclicResolution.Composition

/-!
# Exact base change computed with arbitrary right resolutions

This file states a proposition; it does not prove it.

For the published base change transformation `ExactBaseChange.baseChangeNatTrans τ n`, the
proposition `ResolutionCompatibilityStatement` asserts

* a formula for its component at `A`, after the resolution comparison of an arbitrary right
  resolution `ε : A[0] ⟶ K`, in terms of an arbitrary right resolution `ε' : (α A)[0] ⟶ K'`,
  a cochain map `ψ : α K ⟶ K'` compatible with the augmentations, and the cochain map
  `Φ : β (F₁ K) ⟶ F₂ K'` with components `τ.app (K.X q) ≫ F₂.map (ψ.f q)`;
* that this component is an isomorphism when `F₁` and `F₂` are left exact, the terms of `K`
  and `K'` are acyclic for them, and `Φ` is a quasi-isomorphism.

It is an internal assertion motivated by Stacks Project, Lemma 02N7; see the paired Markdown.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.ExactBaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- For a square of additive functors with exact horizontal functors `α` and `β` and a natural
transformation `τ : F₁ ⋙ β ⟶ α ⋙ F₂`, arbitrary right resolutions `ε` of `A` and `ε'` of `α A`,
an augmentation-compatible cochain map `ψ : α K ⟶ K'`, and a cochain map `Φ : β (F₁ K) ⟶ F₂ K'`
with components `τ.app (K.X q) ≫ F₂.map (ψ.f q)`:
* in every degree `n`, `β` of the resolution comparison of `ε` for `F₁`, followed by the
  component at `A` of `baseChangeNatTrans τ n`, is the inverse of `homologyNatTrans β` at
  `F₁ K`, followed by the homology of `Φ` and the resolution comparison of `ε'` for `F₂`;
* if moreover `F₁` and `F₂` preserve finite limits, the terms of `K` and `K'` are acyclic for
  `F₁` and `F₂` respectively, and `Φ` is a quasi-isomorphism, then every component
  `(baseChangeNatTrans τ n).app A` is an isomorphism.
This definition states a proposition and does not prove it. -/
def ResolutionCompatibilityStatement : Prop :=
  ∀ (C₁ : Type u₁) [Category.{v₁} C₁] [Abelian C₁] [HasInjectiveResolutions C₁]
    (C₂ : Type u₂) [Category.{v₂} C₂] [Abelian C₂] [HasInjectiveResolutions C₂]
    (D₁ : Type u₃) [Category.{v₃} D₁] [Abelian D₁]
    (D₂ : Type u₄) [Category.{v₄} D₂] [Abelian D₂]
    (F₁ : C₁ ⥤ D₁) [F₁.Additive] (F₂ : C₂ ⥤ D₂) [F₂.Additive]
    (α : C₁ ⥤ C₂) [α.Additive] [PreservesFiniteLimits α] [α.PreservesHomology]
    (β : D₁ ⥤ D₂) [β.Additive] [PreservesFiniteLimits β] [β.PreservesHomology]
    (τ : F₁ ⋙ β ⟶ α ⋙ F₂)
    (A : C₁) (K : CochainComplex C₁ ℕ) (K' : CochainComplex C₂ ℕ)
    (ε : (CochainComplex.single₀ C₁).obj A ⟶ K) [QuasiIso ε]
    (ε' : (CochainComplex.single₀ C₂).obj (α.obj A) ⟶ K') [QuasiIso ε']
    (ψ : (α.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ K'),
    AcyclicResolution.mapResolutionAugmentation α ε ≫ ψ = ε' →
    ∀ (Φ : (β.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ⟶
        (F₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj K'),
      (∀ q : ℕ, Φ.f q = τ.app (K.X q) ≫ F₂.map (ψ.f q)) →
      (∀ n : ℕ,
        β.map (AcyclicResolution.resolutionComparison F₁ ε n) ≫
            (ExactBaseChange.baseChangeNatTrans τ n).app A =
          inv ((LeftExactHomology.homologyNatTrans β (ComplexShape.up ℕ) n).app
              ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) ≫
            (HomologicalComplex.homologyFunctor D₂ (ComplexShape.up ℕ) n).map Φ ≫
              AcyclicResolution.resolutionComparison F₂ ε' n) ∧
      (∀ [PreservesFiniteLimits F₁] [PreservesFiniteLimits F₂],
        (∀ q r : ℕ, IsZero ((F₁.rightDerived (r + 1)).obj (K.X q))) →
        (∀ q r : ℕ, IsZero ((F₂.rightDerived (r + 1)).obj (K'.X q))) →
        QuasiIso Φ →
        ∀ n : ℕ, IsIso ((ExactBaseChange.baseChangeNatTrans τ n).app A))

end Langlands.Cohomology.ExactBaseChange
