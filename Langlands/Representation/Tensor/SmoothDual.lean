import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Langlands.Representation.Tensor.Finite
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.MatrixCoefficient.Definitions

/-! # Smooth duals of finite external tensor products -/

noncomputable section

open scoped TensorProduct

namespace Langlands.FiniteTensor

universe uR uI uG uV

variable {R : Type uR} [CommRing R] {ι : Type uI} [Finite ι]
variable {G : ι → Type uG} [∀ i, Group (G i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The canonical map from tensors of algebraic duals intertwines the external
contragredient action with the algebraic dual of the external tensor action. -/
def dualTensorIntertwiner (ρ : ∀ i, Representation R (G i) (V i)) :
    (external (fun i => (ρ i).dual)).IntertwiningMap (external ρ).dual where
  toLinearMap := PiTensorProduct.dualDistrib
  isIntertwining' g := by
    let := Fintype.ofFinite ι
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro ℓ
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change PiTensorProduct.dualDistrib
        (external (fun i => (ρ i).dual) g (PiTensorProduct.tprod R ℓ))
        (PiTensorProduct.tprod R v) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod R ℓ)
        (external ρ g⁻¹ (PiTensorProduct.tprod R v))
    rw [external_tprod, external_tprod, PiTensorProduct.dualDistrib_apply,
      PiTensorProduct.dualDistrib_apply]
    rfl

variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]

/-- The canonical intertwiner from the external tensor of smooth contragredients
into the smooth contragredient of the external tensor. -/
def smoothDualTensorIntertwiner (ρ : ∀ i, Representation R (G i) (V i)) :
    (external (fun i => smoothContragredient (ρ i))).IntertwiningMap
      (smoothContragredient (external ρ)) :=
  smoothLift
    (isSmooth_external _ (fun i => isSmooth_smoothContragredient (ρ i)))
    ((dualTensorIntertwiner ρ).comp (externalMap (fun i => smoothInclusion (ρ i).dual)))

/-- The canonical linear map from the actual finite tensor of smooth duals to
the smooth dual of the actual external tensor product. -/
def smoothDualTensorMap (ρ : ∀ i, Representation R (G i) (V i)) :
    (⨂[R] i, SmoothDual (ρ i)) →ₗ[R] SmoothDual (external ρ) :=
  (smoothDualTensorIntertwiner ρ).toLinearMap

/-- Forgetting smoothness gives Mathlib's canonical dual tensor map applied to
the tensor of the inclusions of the smooth duals. -/
theorem smoothDualTensorMap_val (ρ : ∀ i, Representation R (G i) (V i))
    (x : ⨂[R] i, SmoothDual (ρ i)) :
    (smoothDualTensorMap ρ x).val = PiTensorProduct.dualDistrib
      (PiTensorProduct.map (fun i => smoothDualPairing (ρ i)) x) := rfl

/-- Every functional constructed by the map is smooth for the actual product topology. -/
theorem isSmoothVector_smoothDualTensorMap
    (ρ : ∀ i, Representation R (G i) (V i))
    (x : ⨂[R] i, SmoothDual (ρ i)) :
    IsSmoothVector (external ρ).dual (smoothDualTensorMap ρ x).val :=
  (smoothDualTensorMap ρ x).property

/-- On pure families the canonical functional evaluates as the finite product
of the factor evaluations, including the empty product. -/
@[simp]
theorem smoothDualTensorMap_tprod_apply [Fintype ι]
    (ρ : ∀ i, Representation R (G i) (V i))
    (ℓ : ∀ i, SmoothDual (ρ i)) (v : ∀ i, V i) :
    smoothDualPairing (external ρ)
      (smoothDualTensorMap ρ (PiTensorProduct.tprod R ℓ))
      (PiTensorProduct.tprod R v) = ∏ i, smoothDualPairing (ρ i) (ℓ i) (v i) := by
  change (smoothDualTensorMap ρ (PiTensorProduct.tprod R ℓ)).val
    (PiTensorProduct.tprod R v) = _
  rw [smoothDualTensorMap_val, PiTensorProduct.map_tprod,
    PiTensorProduct.dualDistrib_apply]

/-- Equivariance of the canonical linear map. -/
theorem smoothDualTensorMap_action (ρ : ∀ i, Representation R (G i) (V i))
    (g : ∀ i, G i) (x : ⨂[R] i, SmoothDual (ρ i)) :
    smoothDualTensorMap ρ (external (fun i => smoothContragredient (ρ i)) g x) =
      smoothContragredient (external ρ) g (smoothDualTensorMap ρ x) :=
  (smoothDualTensorIntertwiner ρ).isIntertwining _ _ g x

/-- The actual matrix coefficient of pure tensor vectors and pure smooth
functionals is the product of the factor matrix coefficients. -/
theorem matrixCoefficient_smoothDualTensorMap_tprod [Fintype ι]
    (ρ : ∀ i, Representation R (G i) (V i))
    (ℓ : ∀ i, SmoothDual (ρ i)) (v : ∀ i, V i) (g : ∀ i, G i) :
    matrixCoefficient (external ρ)
      (smoothDualPairing (external ρ) (smoothDualTensorMap ρ (PiTensorProduct.tprod R ℓ)))
      (PiTensorProduct.tprod R v) g =
        ∏ i, matrixCoefficient (ρ i) (smoothDualPairing (ρ i) (ℓ i)) (v i) (g i) := by
  change smoothDualPairing (external ρ)
      (smoothDualTensorMap ρ (PiTensorProduct.tprod R ℓ))
      (external ρ g (PiTensorProduct.tprod R v)) = _
  rw [external_tprod, smoothDualTensorMap_tprod_apply]
  rfl

end Langlands.FiniteTensor
