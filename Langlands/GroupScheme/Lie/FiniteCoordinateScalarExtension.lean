import Langlands.GroupScheme.Lie.FiniteAction
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Scalar extension from natural finite Lie coordinates -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Lie.FiniteCoordinates

variable {R : CommRingCat.{u}} {U : GroupScheme (Spec R)}
    [IsAffineHom U.X.hom] {d : ℕ} (c : Lie.FiniteCoordinates U d)

/-- Natural finite coordinates identify the actual Lie kernel with scalar extension. -/
def scalarExtension (A : CommAlgCat.{u} R) :
    A ⊗[R] Additive (lieKernel U R) ≃ₗ[A] Additive (lieKernel U A) :=
  ((c.equiv (.of R R)).baseChange R A _ _).trans
    ((TensorProduct.piScalarRight R A A (Fin d)).trans (c.equiv A).symm)

/-- On pure tensors, this equivalence is the actual coefficient-change map. -/
theorem scalarExtension_tmul (A : CommAlgCat.{u} R) (a : A)
    (x : Additive (lieKernel U R)) :
    c.scalarExtension A (a ⊗ₜ[R] x) =
      a • lieKernelMapLinear U (Algebra.ofId R A) x := by
  apply (c.equiv A).injective
  simp only [scalarExtension, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, map_smul]
  let f : CommAlgCat.of R R ⟶ A := CommAlgCat.ofHom (Algebra.ofId R A)
  have hn := c.naturality f x
  change (fun j => (c.equiv (.of R R)) x j • a) =
    a • c.equiv A (lieKernelMapLinear U f.hom x)
  rw [hn]
  funext i
  simp [Pi.smul_apply, Algebra.smul_def, f, Algebra.ofId_apply, mul_comm]

/-- Extend any base-ring basis to a basis of the actual Lie kernel on a test algebra. -/
def baseChangeBasis {J : Type*} (b : Module.Basis J R (Additive (lieKernel U R)))
    (A : CommAlgCat.{u} R) : Module.Basis J A (Additive (lieKernel U A)) :=
  (b.baseChange A).map (c.scalarExtension A)

@[simp] theorem baseChangeBasis_apply {J : Type*}
    (b : Module.Basis J R (Additive (lieKernel U R)))
    (A : CommAlgCat.{u} R) (i : J) :
    c.baseChangeBasis b A i = lieKernelMapLinear U (Algebra.ofId R A) (b i) := by
  simp [baseChangeBasis, scalarExtension_tmul]

end Langlands.GroupScheme.Lie.FiniteCoordinates
