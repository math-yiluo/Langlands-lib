import Langlands.Shimura.Unitary.ImaginaryQuadraticTensor

/-! # Natural complementary idempotents in the imaginary quadratic tensor algebra -/

noncomputable section

open NumberField Algebra
open scoped TensorProduct

set_option autoImplicit false

universe u v w w'

namespace Langlands.Shimura.ImaginaryQuadratic

variable (L : Type u) [Field L] [NumberField L] [IsCMField L]
  (K : Type v) [Field K] [CharZero K] [Algebra L K]
  [IsQuadraticExtension ℚ L]
  (R : Type w) [CommRing R] [Algebra K R] [Algebra ℚ R]
  [IsScalarTower ℚ K R]
  (R' : Type w') [CommRing R'] [Algebra K R'] [Algebra ℚ R']
  [IsScalarTower ℚ K R']

/-- The actual map of tensor algebras induced by a coefficient-algebra map. -/
def coefficientMap (f : R →ₐ[K] R') : R ⊗[ℚ] L →ₐ[ℚ] R' ⊗[ℚ] L :=
  Algebra.TensorProduct.map (f.restrictScalars ℚ) (AlgHom.id ℚ L)

omit [IsCMField L] [Algebra L K] [IsQuadraticExtension ℚ L] in
@[simp]
theorem coefficientMap_tmul (f : R →ₐ[K] R') (r : R) (t : L) :
    coefficientMap L K R R' f (r ⊗ₜ[ℚ] t) = f r ⊗ₜ[ℚ] t := rfl

/-- The natural/conjugate splitting commutes with every coefficient-algebra map. -/
theorem algebraEquiv_naturality (f : R →ₐ[K] R') (x : R ⊗[ℚ] L) :
    algebraEquiv L K R' (coefficientMap L K R R' f x) =
      AlgHom.prodMap f f (algebraEquiv L K R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r t =>
    simp [algebraEquiv_tmul, AlgHom.prodMap, f.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The natural (`false`) or conjugate (`true`) coordinate idempotent. -/
def factorIdempotent (conjugate : Bool) : R ⊗[ℚ] L :=
  (algebraEquiv L K R).symm (if conjugate then (0, 1) else (1, 0))

@[simp]
theorem algebraEquiv_factorIdempotent (conjugate : Bool) :
    algebraEquiv L K R (factorIdempotent L K R conjugate) =
      (if conjugate then (0, 1) else (1, 0)) :=
  (algebraEquiv L K R).apply_symm_apply _

/-- Both factors are idempotent, with no nontriviality hypothesis on the coefficients. -/
theorem factorIdempotent_mul_self (conjugate : Bool) :
    factorIdempotent L K R conjugate * factorIdempotent L K R conjugate =
      factorIdempotent L K R conjugate := by
  apply (algebraEquiv L K R).injective
  cases conjugate <;> simp

/-- The two coordinate idempotents are orthogonal. -/
theorem factorIdempotent_mul_other (conjugate : Bool) :
    factorIdempotent L K R conjugate * factorIdempotent L K R (!conjugate) = 0 := by
  apply (algebraEquiv L K R).injective
  cases conjugate <;> simp

/-- The two coordinate idempotents sum to the identity. -/
theorem factorIdempotent_add_other (conjugate : Bool) :
    factorIdempotent L K R conjugate + factorIdempotent L K R (!conjugate) = 1 := by
  apply (algebraEquiv L K R).injective
  cases conjugate <;> simp

/-- Every coefficient-algebra map preserves the actual factor idempotents. -/
theorem coefficientMap_factorIdempotent (f : R →ₐ[K] R') (conjugate : Bool) :
    coefficientMap L K R R' f (factorIdempotent L K R conjugate) =
      factorIdempotent L K R' conjugate := by
  apply (algebraEquiv L K R').injective
  rw [algebraEquiv_naturality, algebraEquiv_factorIdempotent,
    algebraEquiv_factorIdempotent]
  cases conjugate <;> simp [AlgHom.prodMap]

/-- The scalar character belonging to one coordinate of the actual splitting. -/
def factorCharacter (conjugate : Bool) : L →+* R :=
  if conjugate then
    (algebraMap K R).comp
      ((algebraMap L K).comp (IsCMField.complexConj L).toRingHom)
  else (algebraMap K R).comp (algebraMap L K)

/-- Evaluation at the natural (`false`) or conjugate (`true`) coordinate. -/
def factorEvaluation (conjugate : Bool) : R ⊗[ℚ] L →ₐ[R] R :=
  (if conjugate then AlgHom.snd R R R else AlgHom.fst R R R).comp
    (algebraEquiv L K R).toAlgHom

@[simp]
theorem factorEvaluation_tmul (conjugate : Bool) (r : R) (t : L) :
    factorEvaluation L K R conjugate (r ⊗ₜ[ℚ] t) =
      r * factorCharacter L K R conjugate t := by
  cases conjugate <;> simp [factorEvaluation, factorCharacter]

/-- Multiplication by a coordinate idempotent retains exactly that scalar coordinate. -/
theorem mul_factorIdempotent (conjugate : Bool) (x : R ⊗[ℚ] L) :
    x * factorIdempotent L K R conjugate =
      factorEvaluation L K R conjugate x • factorIdempotent L K R conjugate := by
  apply (algebraEquiv L K R).injective
  cases conjugate <;> apply Prod.ext <;> simp [factorEvaluation, Algebra.smul_def]

/-- The tensor algebra is reconstructed from its two scalar coordinates and idempotents. -/
theorem factor_reconstruction (x : R ⊗[ℚ] L) :
    factorEvaluation L K R false x • factorIdempotent L K R false +
      factorEvaluation L K R true x • factorIdempotent L K R true = x := by
  apply (algebraEquiv L K R).injective
  simp [factorEvaluation, Algebra.smul_def]

/-- Imaginary-field multiplication on each idempotent is its natural or conjugate scalar. -/
theorem tmul_mul_factorIdempotent (conjugate : Bool) (t : L) :
    ((1 : R) ⊗ₜ[ℚ] t) * factorIdempotent L K R conjugate =
      factorCharacter L K R conjugate t • factorIdempotent L K R conjugate := by
  simpa using mul_factorIdempotent L K R conjugate ((1 : R) ⊗ₜ[ℚ] t)

end Langlands.Shimura.ImaginaryQuadratic
