import Langlands.Analysis.FrechetOpenMapping
import Langlands.Representation.Archimedean.SmoothDerivativeBasisTopology
import Langlands.Representation.Archimedean.SmoothDerivativeCompleteness

/-! # Open mapping for genuine smooth carriers of Banach representations -/

noncomputable section

open scoped Manifold Topology Uniformity

set_option autoImplicit false

namespace Langlands.Archimedean.DerivativeSmoothVectors

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {R : Aˣ →* (E →L[ℂ] E)} {S : Aˣ →* (F →L[ℂ] F)}

local notation "I" => 𝓘(ℝ, A)

/-- A surjective continuous linear map between genuine smooth carriers of jointly
continuous Banach representations of algebra units is open for the word topologies. -/
theorem isOpenMap_of_surjective_units (hR : IsContinuousRepresentation R)
    (hS : IsContinuousRepresentation S)
    (T : DerivativeSmoothVectors I R →L[ℂ] DerivativeSmoothVectors I S)
    (hT : Function.Surjective T) : IsOpenMap T := by
  let : TopologicalSpace.MetrizableSpace (DerivativeSmoothVectors I R) :=
    metrizableSpace_of_finiteDimensional I R
  let : TopologicalSpace.MetrizableSpace (DerivativeSmoothVectors I S) :=
    metrizableSpace_of_finiteDimensional I S
  let : CompleteSpace (DerivativeSmoothVectors I R) :=
    completeSpace_of_isContinuousRepresentation_units R hR
  let : CompleteSpace (DerivativeSmoothVectors I S) :=
    completeSpace_of_isContinuousRepresentation_units S hS
  let : (𝓤 (DerivativeSmoothVectors I S)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  let : BaireSpace (DerivativeSmoothVectors I S) := inferInstance
  exact Langlands.Analysis.frechetOpenMapping _ _ (T.restrictScalars ℝ) hT

end Langlands.Archimedean.DerivativeSmoothVectors
