import Langlands.Shimura.Unitary.ImaginaryQuadraticModule

/-! # Scalar-extension factors and the actual imaginary quadratic eigensubmodules -/

noncomputable section

open NumberField Algebra
open scoped TensorProduct

set_option autoImplicit false

universe u v w z

namespace Langlands.Shimura.ImaginaryQuadratic

variable (L : Type u) [Field L] [NumberField L] [IsCMField L]
  (K : Type v) [Field K] [CharZero K] [Algebra L K]
  [IsQuadraticExtension ℚ L]
  (R : Type w) [CommRing R] [Algebra K R] [Algebra ℚ R]
  [IsScalarTower ℚ K R]
  (M : Type z) [AddCommGroup M] [Module R M] [Module ℚ M]
  [IsScalarTower ℚ R M]
  (ρ : L →+* Module.End R M)

/-- The actual tensor-algebra module structure induced by the given field action. -/
@[instance_reducible]
def tensorModule : Module (R ⊗[ℚ] L) M :=
  Module.compHom M (tensorAction L R M ρ).toRingHom

/-- The scalar algebra structure for the natural or conjugate coordinate. -/
@[instance_reducible]
def factorAlgebra (conjugate : Bool) : Algebra (R ⊗[ℚ] L) R :=
  (factorEvaluation L K R conjugate).toRingHom.toAlgebra

section TensorFactor

variable (conjugate : Bool)

omit [IsCMField L] [IsQuadraticExtension ℚ L] in
/-- The induced tensor action commutes with the coefficient scalars. -/
theorem tensorModuleTower :
    letI := tensorModule L R M ρ
    IsScalarTower R (R ⊗[ℚ] L) M := by
  let := tensorModule L R M ρ
  exact ⟨fun r a m => by
    change tensorAction L R M ρ (r • a) m = r • tensorAction L R M ρ a m
    rw [map_smul, LinearMap.smul_apply]⟩

/-- The selected coordinate is compatible with coefficient scalars. -/
theorem factorAlgebraTower :
    letI := factorAlgebra L K R conjugate
    IsScalarTower R (R ⊗[ℚ] L) R := by
  let := factorAlgebra L K R conjugate
  exact ⟨fun r a x => by
    change factorEvaluation L K R conjugate (r • a) * x =
      r * (factorEvaluation L K R conjugate a * x)
    rw [map_smul]
    exact mul_assoc r _ x⟩

/-- The coordinate action on the actual eigensubmodule. -/
@[instance_reducible]
def factorEigenModule : Module (R ⊗[ℚ] L) (eigenmodule L K R M ρ conjugate) :=
  Module.compHom (eigenmodule L K R M ρ conjugate)
    (factorEvaluation L K R conjugate).toRingHom

omit [Module ℚ M] [IsScalarTower ℚ R M] in
/-- The coordinate action is the restriction of the coefficient action. -/
theorem factorEigenTower :
    letI := factorAlgebra L K R conjugate
    letI := factorEigenModule L K R M ρ conjugate
    IsScalarTower (R ⊗[ℚ] L) R (eigenmodule L K R M ρ conjugate) := by
  let := factorAlgebra L K R conjugate
  let := factorEigenModule L K R M ρ conjugate
  exact ⟨fun a r m => by
    apply Subtype.ext
    exact mul_smul (factorEvaluation L K R conjugate a) r m.val⟩

/-- The actual projector is linear for the tensor action on the source and
the selected scalar evaluation on the target. -/
def tensorProjector :
    letI := tensorModule L R M ρ
    letI := factorAlgebra L K R conjugate
    letI := tensorModuleTower L R M ρ
    letI := factorAlgebraTower L K R conjugate
    letI := factorEigenModule L K R M ρ conjugate
    letI := factorEigenTower L K R M ρ conjugate
    M →ₗ[R ⊗[ℚ] L] eigenmodule L K R M ρ conjugate := by
  letI := tensorModule L R M ρ
  letI := factorAlgebra L K R conjugate
  letI := tensorModuleTower L R M ρ
  letI := factorAlgebraTower L K R conjugate
  letI := factorEigenModule L K R M ρ conjugate
  letI := factorEigenTower L K R M ρ conjugate
  exact {
  toFun m := ⟨moduleProjector L K R M ρ conjugate m,
    moduleProjector_mem L K R M ρ conjugate m⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ x y
  map_smul' a m := by
    apply Subtype.ext
    change tensorAction L R M ρ (factorIdempotent L K R conjugate)
        (tensorAction L R M ρ a m) =
      factorEvaluation L K R conjugate a • moduleProjector L K R M ρ conjugate m
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
    exact tensorAction_apply_of_mem L K R M ρ conjugate
      (moduleProjector_mem L K R M ρ conjugate m) a }

/-- Scalar extension along either actual coordinate maps to its eigensubmodule
by the corresponding projector. -/
def tensorFactorToEigen :
    letI := tensorModule L R M ρ
    letI := factorAlgebra L K R conjugate
    letI := tensorModuleTower L R M ρ
    letI := factorAlgebraTower L K R conjugate
    letI := factorEigenModule L K R M ρ conjugate
    letI := factorEigenTower L K R M ρ conjugate
    R ⊗[R ⊗[ℚ] L] M →ₗ[R] eigenmodule L K R M ρ conjugate := by
  letI := tensorModule L R M ρ
  letI := factorAlgebra L K R conjugate
  letI := tensorModuleTower L R M ρ
  letI := factorAlgebraTower L K R conjugate
  letI := factorEigenModule L K R M ρ conjugate
  letI := factorEigenTower L K R M ρ conjugate
  exact (tensorProjector L K R M ρ conjugate).liftBaseChange R

@[simp]
theorem tensorFactorToEigen_tmul (r : R) (m : M) :
    letI := tensorModule L R M ρ
    letI := factorAlgebra L K R conjugate
    letI := tensorModuleTower L R M ρ
    letI := factorAlgebraTower L K R conjugate
    letI := factorEigenModule L K R M ρ conjugate
    letI := factorEigenTower L K R M ρ conjugate
    (tensorFactorToEigen L K R M ρ conjugate (r ⊗ₜ[R ⊗[ℚ] L] m)).val =
      r • moduleProjector L K R M ρ conjugate m := by
  let := tensorModule L R M ρ
  let := factorAlgebra L K R conjugate
  let := tensorModuleTower L R M ρ
  let := factorAlgebraTower L K R conjugate
  let := factorEigenModule L K R M ρ conjugate
  let := factorEigenTower L K R M ρ conjugate
  rfl

/-- Tensor balancing identifies a vector with its selected projector after
scalar extension along that coordinate. -/
theorem tmul_moduleProjector (r : R) (m : M) :
    letI := tensorModule L R M ρ
    letI := factorAlgebra L K R conjugate
    letI := tensorModuleTower L R M ρ
    letI := factorAlgebraTower L K R conjugate
    letI := factorEigenModule L K R M ρ conjugate
    letI := factorEigenTower L K R M ρ conjugate
    r ⊗ₜ[R ⊗[ℚ] L] moduleProjector L K R M ρ conjugate m =
      r ⊗ₜ[R ⊗[ℚ] L] m := by
  let := tensorModule L R M ρ
  let := factorAlgebra L K R conjugate
  let := tensorModuleTower L R M ρ
  let := factorAlgebraTower L K R conjugate
  let := factorEigenModule L K R M ρ conjugate
  let := factorEigenTower L K R M ρ conjugate
  change r ⊗ₜ[R ⊗[ℚ] L] (factorIdempotent L K R conjugate • m) = _
  rw [← TensorProduct.smul_tmul]
  change (factorEvaluation L K R conjugate (factorIdempotent L K R conjugate) * r)
    ⊗ₜ[R ⊗[ℚ] L] m = _
  have he : factorEvaluation L K R conjugate (factorIdempotent L K R conjugate) = 1 := by
    cases conjugate <;> simp [factorEvaluation]
  rw [he, one_mul]

/-- The projector-induced tensor map has inverse `m ↦ 1 ⊗ m`. -/
theorem tensorFactorToEigen_leftInverse :
    letI := tensorModule L R M ρ
    letI := factorAlgebra L K R conjugate
    letI := tensorModuleTower L R M ρ
    letI := factorAlgebraTower L K R conjugate
    letI := factorEigenModule L K R M ρ conjugate
    letI := factorEigenTower L K R M ρ conjugate
    Function.LeftInverse
      (fun m : eigenmodule L K R M ρ conjugate => (1 : R) ⊗ₜ[R ⊗[ℚ] L] m.val)
      (tensorFactorToEigen L K R M ρ conjugate) := by
  let := tensorModule L R M ρ
  let := factorAlgebra L K R conjugate
  let := tensorModuleTower L R M ρ
  let := factorAlgebraTower L K R conjugate
  let := factorEigenModule L K R M ρ conjugate
  let := factorEigenTower L K R M ρ conjugate
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r m =>
    change (1 : R) ⊗ₜ[R ⊗[ℚ] L] (r • moduleProjector L K R M ρ conjugate m) =
      r ⊗ₜ[R ⊗[ℚ] L] m
    rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
    exact tmul_moduleProjector L K R M ρ conjugate r m
  | add x y hx hy =>
    change (1 : R) ⊗ₜ[R ⊗[ℚ] L]
        (tensorFactorToEigen L K R M ρ conjugate (x + y)).val = x + y
    rw [map_add]
    change (1 : R) ⊗ₜ[R ⊗[ℚ] L]
        ((tensorFactorToEigen L K R M ρ conjugate x).val +
          (tensorFactorToEigen L K R M ρ conjugate y).val) = x + y
    rw [TensorProduct.tmul_add]
    exact congrArg₂ (· + ·) hx hy

/-- The actual scalar-extension tensor factor is linearly equivalent to the
full simultaneous scalar eigensubmodule. -/
def tensorFactorEquiv :
    letI := tensorModule L R M ρ
    letI := factorAlgebra L K R conjugate
    letI := tensorModuleTower L R M ρ
    letI := factorAlgebraTower L K R conjugate
    letI := factorEigenModule L K R M ρ conjugate
    letI := factorEigenTower L K R M ρ conjugate
    R ⊗[R ⊗[ℚ] L] M ≃ₗ[R] eigenmodule L K R M ρ conjugate := by
  letI := tensorModule L R M ρ
  letI := factorAlgebra L K R conjugate
  letI := tensorModuleTower L R M ρ
  letI := factorAlgebraTower L K R conjugate
  letI := factorEigenModule L K R M ρ conjugate
  letI := factorEigenTower L K R M ρ conjugate
  exact LinearEquiv.ofBijective (tensorFactorToEigen L K R M ρ conjugate)
    ⟨(tensorFactorToEigen_leftInverse L K R M ρ conjugate).injective, by
      intro m
      refine ⟨(1 : R) ⊗ₜ[R ⊗[ℚ] L] m.val, ?_⟩
      apply Subtype.ext
      change (1 : R) • moduleProjector L K R M ρ conjugate m.val = m.val
      rw [one_smul, moduleProjector_apply_of_mem L K R M ρ conjugate m.property]⟩

@[simp]
theorem tensorFactorEquiv_tmul (r : R) (m : M) :
    letI := tensorModule L R M ρ
    letI := factorAlgebra L K R conjugate
    letI := tensorModuleTower L R M ρ
    letI := factorAlgebraTower L K R conjugate
    letI := factorEigenModule L K R M ρ conjugate
    letI := factorEigenTower L K R M ρ conjugate
    (tensorFactorEquiv L K R M ρ conjugate (r ⊗ₜ[R ⊗[ℚ] L] m)).val =
      r • moduleProjector L K R M ρ conjugate m := by
  let := tensorModule L R M ρ
  let := factorAlgebra L K R conjugate
  let := tensorModuleTower L R M ρ
  let := factorAlgebraTower L K R conjugate
  let := factorEigenModule L K R M ρ conjugate
  let := factorEigenTower L K R M ρ conjugate
  rfl

/-- The inverse of the constructed tensor-factor comparison is the canonical tensor map. -/
theorem tensorFactorEquiv_symm_apply (m : eigenmodule L K R M ρ conjugate) :
    letI := tensorModule L R M ρ
    letI := factorAlgebra L K R conjugate
    letI := tensorModuleTower L R M ρ
    letI := factorAlgebraTower L K R conjugate
    letI := factorEigenModule L K R M ρ conjugate
    letI := factorEigenTower L K R M ρ conjugate
    (tensorFactorEquiv L K R M ρ conjugate).symm m =
      (1 : R) ⊗ₜ[R ⊗[ℚ] L] m.val := by
  let := tensorModule L R M ρ
  let := factorAlgebra L K R conjugate
  let := tensorModuleTower L R M ρ
  let := factorAlgebraTower L K R conjugate
  let := factorEigenModule L K R M ρ conjugate
  let := factorEigenTower L K R M ρ conjugate
  apply (tensorFactorEquiv L K R M ρ conjugate).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change m.val = (1 : R) • moduleProjector L K R M ρ conjugate m.val
  rw [one_smul, moduleProjector_apply_of_mem L K R M ρ conjugate m.property]

end TensorFactor

end Langlands.Shimura.ImaginaryQuadratic
