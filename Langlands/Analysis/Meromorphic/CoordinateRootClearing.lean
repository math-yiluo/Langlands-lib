import Langlands.Analysis.Meromorphic.CoordinateGluing

/-! # Common coordinate domains and local root products -/

noncomputable section

open Set Filter
open scoped Manifold

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

variable {X Y κ : Type*} [AddCommGroup X] [Module ℂ X] {n : ℕ}
  (roots : Set κ) (rootForm : κ → X →ₗ[ℂ] ℂ) (f : X → Y → ℂ)

/-- A local product of the prescribed linear forms clears all scalar evaluations
on the part of one neighborhood lying in a locally dense agreement set. -/
def HasLocalRootClearing (e : (Fin n → ℂ) ≃ₗ[ℂ] X) (s₀ : Fin n → ℂ) : Prop :=
  ∃ D W : Set (Fin n → ℂ), IsOpen W ∧ s₀ ∈ W ∧ W ⊆ closure D ∧
    ∃ (S : Finset κ) (m : ℕ), (S : Set κ) ⊆ roots ∧
      ∀ y, ∃ h : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
        EqOn h (fun s => (∏ β ∈ S, rootForm β (e s - e s₀)) ^ m * f (e s) y) (W ∩ D)

/-- A power of a finite product of centered linear forms is entire in coordinates. -/
theorem differentiable_centeredLinearProduct (e : (Fin n → ℂ) ≃ₗ[ℂ] X)
    (s₀ : Fin n → ℂ) (S : Finset κ) (k : ℕ) :
    Differentiable ℂ (fun s => (∏ β ∈ S, rootForm β (e s - e s₀)) ^ k) := by
  classical
  have hlin (β : κ) : Differentiable ℂ (fun s => rootForm β (e s - e s₀)) := by
    simp only [map_sub]
    exact ((rootForm β).comp e.toLinearMap).toContinuousLinearMap.differentiable.sub
      (differentiable_const (rootForm β (e s₀)))
  have hprod (A : Finset κ) : Differentiable ℂ (fun s => ∏ β ∈ A, rootForm β (e s - e s₀)) := by
    induction A using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using differentiable_const (1 : ℂ)
    | insert β A hβ ih =>
      simp only [Finset.prod_insert hβ]
      exact (hlin β).mul ih
  exact (hprod S).pow k

/-- Local scalar meromorphic data and common pole clearing in one coordinate
system give one meromorphy domain and the same local clearing property in every
linear coordinate system. -/
theorem exists_meromorphicInCoordinatesOn_of_local_rootClearing [FiniteDimensional ℂ X]
    (e₀ : (Fin n → ℂ) ≃ₗ[ℂ] X)
    (hmero : ∀ s, HasLocalMeromorphicData (fun y t => f (e₀ t) y) s)
    (hclear : ∀ s, HasLocalRootClearing roots rootForm f e₀ s) :
    ∃ DP : Set X, (∀ y, IsMeromorphicInCoordinatesOn (fun lam => f lam y) DP) ∧
      ∀ (m : ℕ) (e : (Fin m → ℂ) ≃ₗ[ℂ] X) (s₀ : Fin m → ℂ),
        ∃ (S : Finset κ) (k : ℕ) (W : Set (Fin m → ℂ)), (S : Set κ) ⊆ roots ∧
          IsOpen W ∧ s₀ ∈ W ∧ ∀ y, ∃ h : (Fin m → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
          ∀ s ∈ W, e s ∈ DP → h s = (∏ β ∈ S, rootForm β (e s - e s₀)) ^ k * f (e s) y := by
  classical
  obtain ⟨D₀, hD₀⟩ := exists_isMeromorphicOn_of_local hmero
  let DP := e₀ '' D₀
  have hpreimage : e₀ ⁻¹' DP = D₀ := Set.preimage_image_eq D₀ e₀.injective
  have hmer (y : Y) : IsMeromorphicInCoordinatesOn (fun lam => f lam y) DP :=
    isMeromorphicInCoordinatesOn_of_coordinates e₀ (by rw [hpreimage]; exact hD₀ y)
  refine ⟨DP, hmer, fun m e s₀ => ?_⟩
  let T : (Fin m → ℂ) ≃L[ℂ] (Fin n → ℂ) := (e.trans e₀.symm).toContinuousLinearEquiv
  have hT (s : Fin m → ℂ) : e₀ (T s) = e s := by simp [T]
  obtain ⟨D, W, hW, hsW, hWD, S, k, hS, h⟩ := hclear (T s₀)
  refine ⟨S, k, T ⁻¹' W, hS, hW.preimage T.continuous, hsW, fun y => ?_⟩
  obtain ⟨b, hb, hbeq⟩ := h y
  let p (s : Fin n → ℂ) := (∏ β ∈ S, rootForm β (e₀ s - e₀ (T s₀))) ^ k
  have hp : Differentiable ℂ p := differentiable_centeredLinearProduct rootForm e₀ (T s₀) S k
  have hO : IsOpen (W ∩ D₀) := hW.inter (hD₀ y).1
  have heq : EqOn b (fun s => p s * f (e₀ s) y) (W ∩ D₀) := by
    apply EqOn.of_subset_closure (s := (W ∩ D₀) ∩ D)
    · exact fun s hs => hbeq ⟨hs.1.1, hs.2⟩
    · exact (hb.mono inter_subset_left).continuousOn
    · exact hp.continuous.continuousOn.mul
        (((hD₀ y).2.2.1 (ContinuousLinearMap.id ℂ ℂ)).differentiableOn.mono
          inter_subset_right).continuousOn
    · exact inter_subset_left
    · intro s hs
      exact hO.inter_closure ⟨hs, hWD hs.1⟩
  refine ⟨b ∘ T, hb.comp T.differentiable.differentiableOn (fun _ hs => hs), ?_⟩
  intro s hs hsd
  have hsd' : T s ∈ D₀ := by
    have ht : T s ∈ e₀ ⁻¹' DP := by simpa only [mem_preimage, hT] using hsd
    rwa [hpreimage] at ht
  have he := heq ⟨hs, hsd'⟩
  simpa only [Function.comp_apply, p, hT] using he

end Langlands.Analysis.Meromorphic
