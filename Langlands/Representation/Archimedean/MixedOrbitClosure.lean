import Langlands.Representation.Archimedean.MixedOrbitCoefficient
import Langlands.Representation.Archimedean.OrthogonalGroupAveraging

/-! # Invariance of norm closures of derivative-stable compact-stable submodules -/

noncomputable section

open Set
open scoped Classical Manifold ContDiff Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.MixedOrbit

open Langlands.Global Langlands.Global.ArchimedeanGL

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  (ψ : ArchimedeanMatrix K n ≃ₐ[ℝ] A)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R : Aˣ →* (E →L[ℂ] E))
  (Kc : Subgroup Aˣ)

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R
local notation "ε" => DerivativeSmoothVectors.derivativeCLM 𝓜 R []

omit [NumberField K] [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem unitsMap_surjective : Function.Surjective (unitsMap K n ψ) := fun g =>
  ⟨Units.map ψ.symm.toRingEquiv.toRingHom.toMonoidHom g,
    Units.ext (ψ.apply_symm_apply (g : A))⟩

/-- Let `W` be stable under the genuine derivatives in all transported directions and under
a subgroup `Kc`, with each vector annihilated by a monic polynomial in the transported Cartan
square sum. If every connected component of the completion-based group meets the preimage of
`Kc`, then every translate of a vector of `W` lies in the norm closure of the values of `W`. -/
theorem representation_mem_closure_of_stable (hR : IsContinuousRepresentation R)
    (W : Submodule ℂ D)
    (hWX : ∀ (X : RealLieAlgebra K n), ∀ w ∈ W,
      DerivativeSmoothVectors.operator 𝓜 R (ψ (realLieAlgebraToMatrix K n X)) w ∈ W)
    (hWK : ∀ k ∈ Kc, ∀ w ∈ W, DerivativeSmoothVectors.representation 𝓜 R k w ∈ W)
    (hpoly : ∀ w ∈ W, ∃ p : Polynomial ℂ, p.Monic ∧
      Polynomial.aeval (transportedCartanSquareSum K n ψ R) p w = 0)
    (hcover : ∀ x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K),
      ∃ x₀, x ∈ connectedComponent x₀ ∧
        unitsMap K n ψ (archimedeanGLCoordinates K n x₀) ∈ Kc)
    (g : Aˣ) {w : D} (hw : w ∈ W) :
    R g (ε w) ∈ (W.map (ε : D →ₗ[ℂ] E)).topologicalClosure := by
  by_contra hnot
  obtain ⟨L, hL, hne⟩ := exists_functional_vanishing_on_closedSubmodule
    (Submodule.isClosed_topologicalClosure _) hnot
  obtain ⟨u, hu⟩ := unitsMap_surjective K n ψ g
  let x := (archimedeanGLCoordinates K n).symm u
  have hx : unitsMap K n ψ (archimedeanGLCoordinates K n x) = g := by
    simp only [x, ContinuousMulEquiv.apply_symm_apply, hu]
  obtain ⟨x₀, hx₀, hk⟩ := hcover x
  obtain ⟨p, hp, hpw⟩ := hpoly w hw
  have h0 : ∀ w' ∈ W, (orbitCoefficient K n ψ R L w').val x₀ = 0 := by
    intro w' hw'
    rw [orbitCoefficient_apply]
    apply hL
    apply Submodule.le_topologicalClosure
    exact ⟨_, hWK _ hk w' hw', rfl⟩
  have h := orbitCoefficient_eq_zero_of_stable K n ψ R hR L W hWX hw hp hpw x₀ h0 x hx₀
  rw [orbitCoefficient_apply, hx] at h
  exact hne h

end Langlands.Archimedean.MixedOrbit
