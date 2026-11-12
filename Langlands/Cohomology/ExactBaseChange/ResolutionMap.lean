import Langlands.Cohomology.ExactBaseChange.ResolutionStatement
import Langlands.Cohomology.AcyclicResolution.ComparisonProof
import Langlands.Cohomology.ExactBaseChange.ResolutionProof

/-!
# The cochain map of a base-change square on resolutions

For additive functors `F₁ : C₁ ⥤ D₁`, `F₂ : C₂ ⥤ D₂`, `α : C₁ ⥤ C₂`, `β : D₁ ⥤ D₂`, a natural
transformation `τ : F₁ ⋙ β ⟶ α ⋙ F₂`, and a cochain map `ψ : α K ⟶ K'`,
`resolutionBaseChangeMap τ ψ : β (F₁ K) ⟶ F₂ K'` is the cochain map with components
`τ.app (K.X q) ≫ F₂.map (ψ.f q)`, the map `Φ` of the resolution compatibility statement.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.ExactBaseChange

open AcyclicResolution

/-- A right resolution whose terms are acyclic for a left exact `F` has invertible resolution
comparisons. -/
lemma isIso_resolutionComparison_of_acyclic {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasInjectiveResolutions C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] {A : C} {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]
    (hK : ∀ i n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (K.X i))) (n : ℕ) :
    IsIso (resolutionComparison F ε n) :=
  (acyclicResolutionComparisonStatement C D F A K ε inferInstance hK (injectiveResolution A) _
    (comp_lift_id ε _)).2 n

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
  {D₁ : Type u₃} [Category.{v₃} D₁] [Abelian D₁]
  {D₂ : Type u₄} [Category.{v₄} D₂] [Abelian D₂]
  {F₁ : C₁ ⥤ D₁} [F₁.Additive] {F₂ : C₂ ⥤ D₂} [F₂.Additive]
  {α : C₁ ⥤ C₂} [α.Additive] {β : D₁ ⥤ D₂} [β.Additive]

/-- The cochain map `β (F₁ K) ⟶ F₂ K'` with components `τ.app (K.X q) ≫ F₂.map (ψ.f q)`. -/
def resolutionBaseChangeMap (τ : F₁ ⋙ β ⟶ α ⋙ F₂) {K : CochainComplex C₁ ℕ}
    {K' : CochainComplex C₂ ℕ} (ψ : (α.mapHomologicalComplex _).obj K ⟶ K') :
    (β.mapHomologicalComplex _).obj ((F₁.mapHomologicalComplex _).obj K) ⟶
      (F₂.mapHomologicalComplex _).obj K' where
  f q := τ.app (K.X q) ≫ F₂.map (ψ.f q)
  comm' i j _ := by
    have hτ := τ.naturality (K.d i j)
    have hψ : ψ.f i ≫ K'.d i j = α.map (K.d i j) ≫ ψ.f j := ψ.comm i j
    dsimp at hτ ⊢
    rw [Category.assoc, ← F₂.map_comp, hψ, F₂.map_comp, ← Category.assoc, ← hτ,
      Category.assoc]

@[simp]
lemma resolutionBaseChangeMap_f (τ : F₁ ⋙ β ⟶ α ⋙ F₂) {K : CochainComplex C₁ ℕ}
    {K' : CochainComplex C₂ ℕ} (ψ : (α.mapHomologicalComplex _).obj K ⟶ K') (q : ℕ) :
    (resolutionBaseChangeMap τ ψ).f q = τ.app (K.X q) ≫ F₂.map (ψ.f q) :=
  rfl

/-- By the resolution compatibility formula (`resolutionCompatibility`), for acyclic resolutions
the component at `A` of the base change transformation is invertible after applying any functor
`γ` exactly when the homology of `resolutionBaseChangeMap τ ψ` is. -/
theorem isIso_map_baseChangeNatTrans_app_iff [HasInjectiveResolutions C₁]
    [HasInjectiveResolutions C₂]
    [PreservesFiniteLimits α] [α.PreservesHomology] [PreservesFiniteLimits β]
    [β.PreservesHomology] [PreservesFiniteLimits F₁] [PreservesFiniteLimits F₂]
    (τ : F₁ ⋙ β ⟶ α ⋙ F₂) {A : C₁} {K : CochainComplex C₁ ℕ} {K' : CochainComplex C₂ ℕ}
    (ε : (CochainComplex.single₀ C₁).obj A ⟶ K) [QuasiIso ε]
    (ε' : (CochainComplex.single₀ C₂).obj (α.obj A) ⟶ K') [QuasiIso ε']
    (ψ : (α.mapHomologicalComplex _).obj K ⟶ K') (hψ : mapResolutionAugmentation α ε ≫ ψ = ε')
    (hK : ∀ q r : ℕ, IsZero ((F₁.rightDerived (r + 1)).obj (K.X q)))
    (hK' : ∀ q r : ℕ, IsZero ((F₂.rightDerived (r + 1)).obj (K'.X q)))
    {E : Type u} [Category.{v} E] (γ : D₂ ⥤ E) (n : ℕ) :
    IsIso (γ.map ((baseChangeNatTrans τ n).app A)) ↔
      IsIso (γ.map ((HomologicalComplex.homologyFunctor D₂ _ n).map
        (resolutionBaseChangeMap τ ψ))) := by
  have h := (resolutionCompatibility.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} C₁ C₂ D₁ D₂ F₁ F₂ α β τ
    A K K' ε ε' ψ hψ (resolutionBaseChangeMap τ ψ) (fun _ => rfl)).1 n
  have := isIso_resolutionComparison_of_acyclic F₁ ε hK n
  have := isIso_resolutionComparison_of_acyclic F₂ ε' hK' n
  rw [← IsIso.eq_inv_comp] at h
  rw [h, γ.map_comp, γ.map_comp, γ.map_comp, isIso_comp_left_iff, isIso_comp_left_iff,
    isIso_comp_right_iff]

end Langlands.Cohomology.ExactBaseChange
