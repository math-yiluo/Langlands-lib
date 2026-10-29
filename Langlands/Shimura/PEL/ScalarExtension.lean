import Langlands.Shimura.PEL.Similitudes
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! # The tensor-algebra action on a scalar-extended PEL source module -/

noncomputable section
open scoped TensorProduct

namespace Langlands.Shimura.PEL

variable (D V R : Type*) [Ring D] [Algebra ℚ D]
  [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  [CommRing R] [Algebra ℚ R]

/-- Extend the given algebra representation and commute the two scalar factors. -/
def scalarExtensionAlgebraAction :
    (D ⊗[ℚ] R) →ₐ[ℚ] Module.End R (R ⊗[ℚ] V) :=
  ((LinearMap.tensorProductEnd ℚ R V).restrictScalars ℚ).comp
    ((Algebra.TensorProduct.map (AlgHom.id ℚ R) (Algebra.lsmul ℚ ℚ V)).comp
      (Algebra.TensorProduct.comm ℚ D R).toAlgHom)

/-- The canonical tensor-algebra action on the usual scalar-extension carrier. -/
@[instance_reducible]
def scalarExtensionAlgebraModule : Module (D ⊗[ℚ] R) (R ⊗[ℚ] V) :=
  Module.compHom _ (scalarExtensionAlgebraAction D V R).toRingHom

/-- Both tensor orientations have their expected action on pure tensors. -/
@[simp]
theorem scalarExtensionAlgebraAction_tmul (d : D) (a r : R) (x : V) :
    scalarExtensionAlgebraAction D V R (d ⊗ₜ[ℚ] a) (r ⊗ₜ[ℚ] x) =
      (a * r) ⊗ₜ[ℚ] (d • x) := by
  simp [scalarExtensionAlgebraAction, LinearMap.tensorProductEnd,
    LinearMap.tensorProduct, TensorProduct.smul_tmul']

theorem scalarExtensionAlgebraModule_tmul_smul (d : D) (a r : R) (x : V) :
    letI := scalarExtensionAlgebraModule D V R
    (d ⊗ₜ[ℚ] a) • (r ⊗ₜ[ℚ] x) = (a * r) ⊗ₜ[ℚ] (d • x) :=
  scalarExtensionAlgebraAction_tmul D V R d a r x

/-- Similitudes of the scalar extension of a rational form, with the actual
extended algebra representation on its carrier. -/
abbrev ScalarExtensionSimilitudes (ψ : LinearMap.BilinForm ℚ V) :=
  letI := scalarExtensionAlgebraModule D V R
  bilinearSimilitudes (D ⊗[ℚ] R) (ψ.baseChange R)

end Langlands.Shimura.PEL
