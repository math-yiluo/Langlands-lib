/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
public import WeilConjectures.CategoryTheory.Exact.ExactClosedDerivedHom
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived

set_option linter.privateModule false
/-! # Tensor compatibility of a square of exact derived functors -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
universe u a b c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory
section TensorMonoidal
open Category Functor.OplaxMonoidal Functor.Monoidal
variable {E H : Type*} [Category E] [Category H]
  [MonoidalCategory E] [MonoidalCategory H]
  {F G : E ⥤ H} [mF : F.Monoidal] [mG : G.Monoidal] (e : F ≅ G)
  (hd : ∀ X Y, e.hom.app (X ⊗ Y) ≫ δ G X Y =
    δ F X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y))
end TensorMonoidal
end CategoryTheory
namespace CategoryTheory
section CompareStructures
open Category Functor.OplaxMonoidal Functor.LaxMonoidal
variable {E H : Type*} [Category E] [Category H]
  [MonoidalCategory E] [MonoidalCategory H] (F : E ⥤ H)
  (m n : F.Monoidal)
  (hd : ∀ X Y, @δ _ _ _ _ _ _ F m.toOplaxMonoidal X Y =
    @δ _ _ _ _ _ _ F n.toOplaxMonoidal X Y)
include hd in
/-- The invertible tensor comparison determines the monoidal structure, including its unit.
Source: the monoidal unit axioms and uniqueness of inverses.
-/
private theorem monoidal_eq_of_delta : m = n := by
  letI := m
  have hu : @η _ _ _ _ _ _ F m.toOplaxMonoidal =
      @η _ _ _ _ _ _ F n.toOplaxMonoidal := by
    apply Functor.eq_of_leftUnitality (δ F (𝟙_ E) (𝟙_ E))
    · exact Functor.OplaxMonoidal.left_unitality_hom F (𝟙_ E)
    · rw [hd]
      exact @Functor.OplaxMonoidal.left_unitality_hom _ _ _ _ _ _ F n.toOplaxMonoidal (𝟙_ E)
  have hμ (X Y : E) : @μ _ _ _ _ _ _ F m.toLaxMonoidal X Y =
      @μ _ _ _ _ _ _ F n.toLaxMonoidal X Y := by
    apply (cancel_mono (δ F X Y)).1
    rw [Functor.Monoidal.μ_δ, hd]
    exact (@Functor.Monoidal.μ_δ _ _ _ _ _ _ F n X Y).symm
  have hε : @ε _ _ _ _ _ _ F m.toLaxMonoidal =
      @ε _ _ _ _ _ _ F n.toLaxMonoidal := by
    apply (cancel_mono (η F)).1
    rw [Functor.Monoidal.ε_η, hu]
    exact (@Functor.Monoidal.ε_η _ _ _ _ _ _ F n).symm
  apply Functor.Monoidal.ext
  · exact hε
  · exact funext fun X ↦ funext fun Y ↦ hμ X Y
  · exact hu
  · exact funext fun X ↦ funext fun Y ↦ hd X Y
end CompareStructures
end CategoryTheory
namespace CategoryTheory.Functor
variable {A : Type a} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type b} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  {C : Type c} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type d} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F₁ : A ⥤ B) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₁.PreservesFlat] [F₁.IsLeftAdjoint] [F₁.Monoidal]
  (F₂ : B ⥤ D) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [F₂.PreservesFlat] [F₂.IsLeftAdjoint] [F₂.Monoidal]
  (G₁ : A ⥤ C) [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₁.PreservesFlat] [G₁.IsLeftAdjoint] [G₁.Monoidal]
  (G₂ : C ⥤ D) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [G₂.PreservesFlat] [G₂.IsLeftAdjoint] [G₂.Monoidal]
  (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) [NatTrans.IsMonoidal τ.hom]
private def pairIso : F₁.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor ≅
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory :=
  isoWhiskerRight F₁.leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
    isoWhiskerLeft _ F₂.leftDerivedFunctorIsoMapDerivedCategory
private theorem exactDerivedMonoidal_eq_of_delta (m : F₁.mapDerivedCategory.Monoidal)
    (hd : ∀ K M, @OplaxMonoidal.δ _ _ _ _ _ _ F₁.mapDerivedCategory
      m.toOplaxMonoidal K M =
      F₁.leftDerivedFunctorIsoMapDerivedCategory.inv.app (K ⊗ M) ≫
        (F₁.leftDerivedTensorComparison.app K).app M ≫
          (F₁.leftDerivedFunctorIsoMapDerivedCategory.hom.app K ⊗ₘ
            F₁.leftDerivedFunctorIsoMapDerivedCategory.hom.app M)) :
    m = exactClosedDerivedMonoidal F₁ := by
  unfold exactClosedDerivedMonoidal
  letI := F₁.residueDerivedMonoidal
  apply monoidal_eq_of_delta
  intro K M
  rw [hd, Functor.Monoidal.transport_δ]
  rfl

end CategoryTheory.Functor
