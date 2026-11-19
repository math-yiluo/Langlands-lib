import Langlands.Representation.Archimedean.SmoothHilbert

/-! # Compact admissibility of the genuine smooth action -/

noncomputable section

open scoped Manifold ContDiff Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

variable {𝔤 : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {M : Type*} [TopologicalSpace M] (I : ModelWithCorners ℝ 𝔤 M)
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace M G] [LieGroup I ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : G →* (E →L[ℂ] E)) (K : Subgroup G)

local notation "D" => DerivativeSmoothVectors I R

/-- Intertwiners from a compact type into the actual smooth-vector action. -/
def smoothIntertwiners (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ) :
    Submodule ℂ ((Fin d → ℂ) →ₗ[ℂ] D) where
  carrier := {T | ∀ (k : K) (x : Fin d → ℂ),
    T (τ k *ᵥ x) = representation I R (k : G) (T x)}
  zero_mem' := by simp
  add_mem' {S T} hS hT := by
    intro k x
    simp [hS k x, hT k x]
  smul_mem' c T hT := by
    intro k x
    simp [hT k x]

/-- Admissibility tested on continuous finite-dimensional matrix types of the compact subgroup. -/
def IsAdmissible : Prop :=
  ∀ (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ), Continuous τ →
    FiniteDimensional ℂ (smoothIntertwiners I R K d τ)

/-- Every smooth intertwiner embeds into the corresponding Banach intertwiner space. -/
theorem isAdmissible_of_norm (h : Langlands.Archimedean.IsAdmissible R K) :
    IsAdmissible I R K := by
  intro d τ hτ
  let E₀ := (derivativeCLM I R []).toLinearMap
  let L : ((Fin d → ℂ) →ₗ[ℂ] D) →ₗ[ℂ] ((Fin d → ℂ) →ₗ[ℂ] E) :=
    LinearMap.llcomp ℂ (Fin d → ℂ) D E E₀
  let j : smoothIntertwiners I R K d τ →ₗ[ℂ] Langlands.Archimedean.intertwiners R K d τ :=
    (L.comp (smoothIntertwiners I R K d τ).subtype).codRestrict
      (Langlands.Archimedean.intertwiners R K d τ) (fun T k x => by
        change E₀ (T.val (τ k *ᵥ x)) = R (k : G) (E₀ (T.val x))
        rw [T.property k x]
        rfl)
  let : FiniteDimensional ℂ (Langlands.Archimedean.intertwiners R K d τ) := h d τ hτ
  refine FiniteDimensional.of_injective
    (V₂ := ↥(Langlands.Archimedean.intertwiners R K d τ)) j ?_
  intro S T he
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply (toSmooth I R).injective
  apply Subtype.ext
  exact congrArg (fun U : Langlands.Archimedean.intertwiners R K d τ => U.val x) he

end Langlands.Archimedean.DerivativeSmoothVectors
