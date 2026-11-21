import Langlands.Representation.Archimedean.SmoothUnitAction

/-! # Genuine derivative operators on the finite vectors of a restricted units action -/

noncomputable section

open scoped Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

variable {A E K : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [NormedSpace ℂ E] [Monoid K]
  (R : Aˣ →* (E →L[ℂ] E)) (j : K →* Aˣ)

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R
local notation "ρ" => MonoidHom.comp (representation 𝓜 R) j
local notation "dR" => operator 𝓜 R
local notation "V" => Subrepresentation.toSubmodule (FiniteVectors.subrepresentation ρ)

/-- Derivative directions preserve finite orbit span for any restriction of the units action. -/
theorem isFiniteVector_operator_units (X : A) {v : D} (hv : FiniteVectors.IsFiniteVector ρ v) :
    FiniteVectors.IsFiniteVector ρ (dR X v) := by
  let W := FiniteVectors.orbitSpan ρ v
  let : FiniteDimensional ℂ W := hv
  let b := Module.finBasis ℝ A
  let T : Submodule ℂ D := ⨆ i, W.map (dR (b i))
  let : FiniteDimensional ℂ T := by
    dsimp only [T]
    infer_instance
  apply Submodule.finiteDimensional_of_le (S₂ := T)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let g := j k
  have h₁ : representation 𝓜 R g⁻¹ (representation 𝓜 R g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h₂ (w : D) : representation 𝓜 R g (representation 𝓜 R g⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h := operator_representation_units R g⁻¹ X (representation 𝓜 R g v)
  rw [h₁] at h
  have h' := congrArg (representation 𝓜 R g) h
  rw [h₂] at h'
  change representation 𝓜 R g (dR X v) ∈ T
  rw [h', operator_eq_sum_basis R b]
  apply T.sum_mem
  intro i _
  apply T.smul_mem ((b.coord i (inverseConjugationCLM g⁻¹ X) : ℝ) : ℂ)
  apply (le_iSup (fun l => W.map (dR (b l))) i)
  exact Submodule.mem_map_of_mem (FiniteVectors.action_mem_orbitSpan ρ k v)

/-- The actual derivative on the finite vectors of the restricted representation. -/
def finiteVectorsOperator (X : A) : Module.End ℂ V :=
  (dR X).restrict fun _ hv => isFiniteVector_operator_units R j X hv

@[simp]
theorem coe_finiteVectorsOperator (X : A) (v : V) :
    ((finiteVectorsOperator R j X v : V) : D) = dR X v := rfl

end Langlands.Archimedean.DerivativeSmoothVectors
