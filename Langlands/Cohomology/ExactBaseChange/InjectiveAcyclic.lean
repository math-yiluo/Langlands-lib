import Langlands.Cohomology.ExactBaseChange.ResolutionProof

/-!
# Exact base change from acyclicity on injective objects

An invertible degree-zero comparison induces isomorphisms in every degree if the exact
source-side functor sends injectives to objects acyclic for the target functor.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.ExactBaseChange

open AcyclicResolution

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasInjectiveResolutions C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasInjectiveResolutions C₂]
  {D₁ : Type u₃} [Category.{v₃} D₁] [Abelian D₁]
  {D₂ : Type u₄} [Category.{v₄} D₂] [Abelian D₂]
  {F₁ : C₁ ⥤ D₁} [F₁.Additive] [PreservesFiniteLimits F₁]
  {F₂ : C₂ ⥤ D₂} [F₂.Additive] [PreservesFiniteLimits F₂]
  {α : C₁ ⥤ C₂} [α.Additive] [PreservesFiniteLimits α] [α.PreservesHomology]
  {β : D₁ ⥤ D₂} [β.Additive] [PreservesFiniteLimits β] [β.PreservesHomology]
  (τ : F₁ ⋙ β ⟶ α ⋙ F₂) [IsIso τ]

/-- If `α` sends injectives to `F₂`-acyclic objects and the degree-zero comparison is an
isomorphism, each component of the derived base change comparison is an isomorphism. -/
theorem isIso_baseChangeNatTrans_app_of_injective_acyclic
    (hα : ∀ (I : C₁) [Injective I] (r : ℕ),
      IsZero ((F₂.rightDerived (r + 1)).obj (α.obj I))) (A : C₁) (n : ℕ) :
    IsIso ((baseChangeNatTrans τ n).app A) := by
  let K := (injectiveResolution A).cocomplex
  have := quasiIso_mapResolutionAugmentation α (injectiveResolution A).ι
  have : IsIso ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app K) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex (asIso τ)
      (ComplexShape.up ℕ)).app K).hom)
  exact isIso_baseChangeNatTrans_app_of_acyclic τ
    (ε := (injectiveResolution A).ι)
    (ε' := mapResolutionAugmentation α (injectiveResolution A).ι)
    (ψ := 𝟙 _)
    (Φ := (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app K)
    (Category.comp_id _)
    (fun q => by simp; rfl)
    (fun q r => F₁.isZero_rightDerived_obj_injective_succ r (K.X q))
    (fun q r => hα (K.X q) r) n

/-- A degree-zero isomorphism and acyclicity of the images of injective objects make the
derived base change comparison a natural isomorphism. -/
theorem isIso_baseChangeNatTrans_of_injective_acyclic
    (hα : ∀ (I : C₁) [Injective I] (r : ℕ),
      IsZero ((F₂.rightDerived (r + 1)).obj (α.obj I))) (n : ℕ) :
    IsIso (baseChangeNatTrans τ n) := by
  have : ∀ A, IsIso ((baseChangeNatTrans τ n).app A) :=
    fun A => isIso_baseChangeNatTrans_app_of_injective_acyclic τ hα A n
  exact NatIso.isIso_of_isIso_app _

/-- The natural isomorphism whose forward map is the published derived base change map. -/
def baseChangeIsoOfInjectiveAcyclic
    (hα : ∀ (I : C₁) [Injective I] (r : ℕ),
      IsZero ((F₂.rightDerived (r + 1)).obj (α.obj I))) (n : ℕ) :
    F₁.rightDerived n ⋙ β ≅ α ⋙ F₂.rightDerived n :=
  haveI := isIso_baseChangeNatTrans_of_injective_acyclic τ hα n
  asIso (baseChangeNatTrans τ n)

end Langlands.Cohomology.ExactBaseChange
