import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionTopology

/-! # Ordered angle seminorms and finite-coordinate smooth tensor topology -/

noncomputable section

open Langlands.Plancherel Langlands.HarmonicAnalysis.TorusFourier
open TopologicalSpace
open scoped TensorProduct

namespace Langlands.HarishChandraSchwartz

universe uJ uV uB uC

variable (J : Type uJ) [Fintype J] [DecidableEq J]

/-- The ordered angle derivative, regarded as a continuous function on the torus. -/
def smoothTorusDerivative (l : List J) :
    smoothFiniteTorusFunctions J →ₗ[ℂ] C(J → Circle, ℂ) :=
  smoothTorusToContinuousMap ∘ₗ torusPartialDerivListLinear l

@[simp]
theorem smoothTorusDerivative_apply (l : List J) (f : smoothFiniteTorusFunctions J)
    (z : J → Circle) :
    smoothTorusDerivative J l f z = torusPartialDerivList l f.val z := by
  exact congrFun (torusPartialDerivListLinear_apply l f) z

/-- Supremum norm of an ordered angle derivative, including order zero. -/
def smoothTorusSeminorm (l : List J) : Seminorm ℂ (smoothFiniteTorusFunctions J) :=
  (normSeminorm ℂ C(J → Circle, ℂ)).comp (smoothTorusDerivative J l)

@[simp]
theorem smoothTorusSeminorm_apply (l : List J) (f : smoothFiniteTorusFunctions J) :
    smoothTorusSeminorm J l f = ‖smoothTorusDerivative J l f‖ := rfl

theorem norm_torusPartialDerivList_le_smoothTorusSeminorm (l : List J)
    (f : smoothFiniteTorusFunctions J) (z : J → Circle) :
    ‖torusPartialDerivList l f.val z‖ ≤ smoothTorusSeminorm J l f := by
  simpa only [smoothTorusDerivative_apply, smoothTorusSeminorm_apply] using
    (ContinuousMap.norm_coe_le_norm (smoothTorusDerivative J l f) z)

theorem smoothTorusSeminorm_le_iff (l : List J) (f : smoothFiniteTorusFunctions J)
    {C : ℝ} (hC : 0 ≤ C) :
    smoothTorusSeminorm J l f ≤ C ↔
      ∀ z, ‖torusPartialDerivList l f.val z‖ ≤ C := by
  rw [smoothTorusSeminorm_apply, ContinuousMap.norm_le _ hC]
  simp only [smoothTorusDerivative_apply]

/-- Independently generated scalar smooth topology; no section topology is used. -/
@[instance_reducible]
def smoothTorusFunctionTopology : TopologicalSpace (smoothFiniteTorusFunctions J) :=
  (SeminormFamily.moduleFilterBasis
    (smoothTorusSeminorm J : SeminormFamily ℂ _ (List J))).topology

/-- A separate, optional derivative-order identification, not a premise of the
section topology targets. -/
def SmoothTorusDerivativePermutationStatement : Prop :=
  ∀ (l m : List J), l.Perm m → ∀ f : smoothFiniteTorusFunctions J,
    torusPartialDerivList l f.val = torusPartialDerivList m f.val

/-- Product of the independently defined scalar smooth topologies. -/
@[instance_reducible]
def smoothTorusProductTopology (B : Type uB) :
    TopologicalSpace (B → smoothFiniteTorusFunctions J) :=
  letI := smoothTorusFunctionTopology J
  inferInstance

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {B : Type uB} [Fintype B] [DecidableEq B] (b : Module.Basis B ℂ V)

/-- Finite coordinates of the algebraic smooth tensor in a coefficient basis. -/
def smoothTensorCoordinates :
    smoothFiniteTorusFunctions J ⊗[ℂ] V ≃ₗ[ℂ] (B → smoothFiniteTorusFunctions J) :=
  (TensorProduct.equivFinsuppOfBasisRight b).trans
    (Finsupp.linearEquivFunOnFinite ℂ (smoothFiniteTorusFunctions J) B)

omit [DecidableEq J] in
theorem smoothTensorCoordinates_apply (t : smoothFiniteTorusFunctions J ⊗[ℂ] V)
    (i : B) (z : J → Circle) :
    (smoothTensorCoordinates J b t i).val z =
      b.coord i (smoothTensorEvaluation J V t z) :=
  smoothTensorEvaluation_basisCoord J V b t i z

/-- Finite-product topology on the common algebraic tensor space, pulled back
along its algebraic basis-coordinate equivalence. -/
@[instance_reducible]
def smoothTensorFiniteProductTopology :
    TopologicalSpace (smoothFiniteTorusFunctions J ⊗[ℂ] V) :=
  induced (smoothTensorCoordinates J b) (smoothTorusProductTopology J B)

/-- Independence of finite basis, expressed on the same algebraic tensor space. -/
def SmoothTensorBasisIndependenceStatement
    {C : Type uC} [Fintype C] [DecidableEq C] (c : Module.Basis C ℂ V) : Prop :=
  smoothTensorFiniteProductTopology J b = smoothTensorFiniteProductTopology J c

end Langlands.HarishChandraSchwartz
