import Langlands.Shimura.Unitary.ImaginaryQuadraticProjectors

/-! # Actual eigensubmodules of an imaginary quadratic action -/

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

/-- The actual tensor-algebra action extending the given commuting imaginary-field action. -/
def tensorAction : R ⊗[ℚ] L →ₐ[R] Module.End R M :=
  AlgHom.liftEquiv ℚ R L _ ρ.toRatAlgHom

omit [IsCMField L] [IsQuadraticExtension ℚ L] in
@[simp]
theorem tensorAction_tmul (r : R) (t : L) :
    tensorAction L R M ρ (r ⊗ₜ[ℚ] t) = r • ρ t := rfl

/-- The simultaneous natural or conjugate scalar eigensubmodule. -/
def eigenmodule (conjugate : Bool) : Submodule R M where
  carrier := {m | ∀ t : L, ρ t m = factorCharacter L K R conjugate t • m}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy t
    simp only [map_add, hx t, hy t, smul_add]
  smul_mem' := by
    intro r x hx t
    rw [map_smul, hx t, smul_comm]

/-- The endomorphism obtained by acting with the actual coordinate idempotent. -/
def moduleProjector (conjugate : Bool) : Module.End R M :=
  tensorAction L R M ρ (factorIdempotent L K R conjugate)

/-- The constructed endomorphisms are idempotent. -/
theorem moduleProjector_mul_self (conjugate : Bool) :
    moduleProjector L K R M ρ conjugate * moduleProjector L K R M ρ conjugate =
      moduleProjector L K R M ρ conjugate := by
  simpa only [moduleProjector, map_mul] using
    congrArg (tensorAction L R M ρ) (factorIdempotent_mul_self L K R conjugate)

/-- The two constructed projectors are orthogonal. -/
theorem moduleProjector_mul_other (conjugate : Bool) :
    moduleProjector L K R M ρ conjugate * moduleProjector L K R M ρ (!conjugate) = 0 := by
  simpa only [moduleProjector, map_mul, map_zero] using
    congrArg (tensorAction L R M ρ) (factorIdempotent_mul_other L K R conjugate)

/-- The two constructed projectors sum to the identity. -/
theorem moduleProjector_add_other (conjugate : Bool) :
    moduleProjector L K R M ρ conjugate + moduleProjector L K R M ρ (!conjugate) = 1 := by
  simpa only [moduleProjector, map_add, map_one] using
    congrArg (tensorAction L R M ρ) (factorIdempotent_add_other L K R conjugate)

/-- The image of each actual projector satisfies the full corresponding eigencondition. -/
theorem moduleProjector_mem (conjugate : Bool) (m : M) :
    moduleProjector L K R M ρ conjugate m ∈ eigenmodule L K R M ρ conjugate := by
  intro t
  have h := congrArg (fun a => tensorAction L R M ρ a m)
    (tmul_mul_factorIdempotent L K R conjugate t)
  simpa only [moduleProjector, map_mul, tensorAction_tmul, one_smul, Module.End.mul_apply,
    map_smul, LinearMap.smul_apply] using h

/-- An eigenvector sees the whole tensor algebra through its actual scalar evaluation. -/
theorem tensorAction_apply_of_mem (conjugate : Bool) {m : M}
    (hm : m ∈ eigenmodule L K R M ρ conjugate) (a : R ⊗[ℚ] L) :
    tensorAction L R M ρ a m = factorEvaluation L K R conjugate a • m := by
  induction a using TensorProduct.inductionOn with
  | tmul r t =>
    simp only [tensorAction_tmul, LinearMap.smul_apply, hm t,
      factorEvaluation_tmul, mul_smul]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb, add_smul]

/-- A vector in the eigensubmodule is fixed by its corresponding projector. -/
theorem moduleProjector_apply_of_mem (conjugate : Bool) {m : M}
    (hm : m ∈ eigenmodule L K R M ρ conjugate) :
    moduleProjector L K R M ρ conjugate m = m := by
  rw [moduleProjector, tensorAction_apply_of_mem L K R M ρ conjugate hm]
  cases conjugate <;> simp [factorEvaluation]

/-- A vector in either eigensubmodule is killed by the other projector. -/
theorem moduleProjector_other_apply_of_mem (conjugate : Bool) {m : M}
    (hm : m ∈ eigenmodule L K R M ρ conjugate) :
    moduleProjector L K R M ρ (!conjugate) m = 0 := by
  rw [moduleProjector, tensorAction_apply_of_mem L K R M ρ conjugate hm]
  cases conjugate <;> simp [factorEvaluation]

/-- The actual image submodule of the projector is exactly the scalar eigensubmodule. -/
theorem range_moduleProjector (conjugate : Bool) :
    LinearMap.range (moduleProjector L K R M ρ conjugate) =
      eigenmodule L K R M ρ conjugate := by
  ext m
  constructor
  · rintro ⟨x, rfl⟩
    exact moduleProjector_mem L K R M ρ conjugate x
  · intro hm
    exact ⟨m, moduleProjector_apply_of_mem L K R M ρ conjugate hm⟩

/-- The actual module splits as the product of its natural and conjugate eigensubmodules. -/
def eigenmoduleEquiv :
    M ≃ₗ[R] eigenmodule L K R M ρ false × eigenmodule L K R M ρ true where
  toFun m :=
    (⟨moduleProjector L K R M ρ false m, moduleProjector_mem L K R M ρ false m⟩,
      ⟨moduleProjector L K R M ρ true m, moduleProjector_mem L K R M ρ true m⟩)
  invFun m := m.1.val + m.2.val
  left_inv m := by
    have h := congrArg (fun f : Module.End R M => f m)
      (moduleProjector_add_other L K R M ρ false)
    simpa only [LinearMap.add_apply, Bool.not_false, Module.End.one_apply] using h
  right_inv m := by
    apply Prod.ext
    · apply Subtype.ext
      change moduleProjector L K R M ρ false (m.1.val + m.2.val) = m.1.val
      rw [map_add, moduleProjector_apply_of_mem L K R M ρ false m.1.property]
      have h := moduleProjector_other_apply_of_mem L K R M ρ true m.2.property
      simp only [Bool.not_true] at h
      rw [h, add_zero]
    · apply Subtype.ext
      change moduleProjector L K R M ρ true (m.1.val + m.2.val) = m.2.val
      rw [map_add, moduleProjector_apply_of_mem L K R M ρ true m.2.property]
      have h := moduleProjector_other_apply_of_mem L K R M ρ false m.1.property
      simp only [Bool.not_false] at h
      rw [h, zero_add]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> exact map_add _ x y
  map_smul' r x := by
    apply Prod.ext <;> apply Subtype.ext <;> exact map_smul _ r x

end Langlands.Shimura.ImaginaryQuadratic
