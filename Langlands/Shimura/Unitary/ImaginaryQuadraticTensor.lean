import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The natural and conjugate splitting of an imaginary quadratic tensor algebra -/

noncomputable section

open NumberField Algebra
open scoped TensorProduct

set_option autoImplicit false

universe u v w

namespace Langlands.Shimura.ImaginaryQuadratic

variable (L : Type u) [Field L] [NumberField L] [IsCMField L]
  (K : Type v) [Field K] [CharZero K] [Algebra L K]

/-- Evaluate at the natural and conjugate inclusions into the containing field. -/
def evaluation : L →ₐ[ℚ] K × K :=
  ((algebraMap L K).prod
    ((algebraMap L K).comp (IsCMField.complexConj L).toRingHom)).toRatAlgHom

/-- Scalar extension of the two actual embeddings. -/
def tensorEvaluation : K ⊗[ℚ] L →ₐ[K] K × K :=
  AlgHom.liftEquiv ℚ K L _ (evaluation L K)

@[simp]
theorem tensorEvaluation_tmul (k : K) (r : L) :
    tensorEvaluation L K (k ⊗ₜ[ℚ] r) =
      (k * algebraMap L K r, k * algebraMap L K (IsCMField.complexConj L r)) := rfl

/-- Two different CM evaluation vectors span the product. -/
theorem tensorEvaluation_surjective : Function.Surjective (tensorEvaluation L K) := by
  have hn : ∃ t : L, t ≠ IsCMField.complexConj L t := by
    by_contra! h
    apply IsCMField.complexConj_ne_one L
    ext t
    exact (h t).symm
  obtain ⟨t, ht⟩ := hn
  let a := algebraMap L K t
  let b := algebraMap L K (IsCMField.complexConj L t)
  have hd : a - b ≠ 0 := sub_ne_zero.mpr (fun h => ht ((algebraMap L K).injective h))
  intro x
  let c := (x.1 - x.2) / (a - b)
  let d := x.1 - c * a
  refine ⟨d ⊗ₜ[ℚ] (1 : L) + c ⊗ₜ[ℚ] t, ?_⟩
  rw [map_add, tensorEvaluation_tmul, tensorEvaluation_tmul]
  apply Prod.ext
  · change d * algebraMap L K 1 + c * a = x.1
    rw [map_one, mul_one]
    dsimp [d]
    ring
  · change d * algebraMap L K (IsCMField.complexConj L 1) + c * b = x.2
    rw [map_one, map_one, mul_one]
    dsimp [d, c]
    field_simp [hd]
    ring

variable [IsQuadraticExtension ℚ L]

/-- Quadratic degree gives injectivity as well as the explicit surjectivity. -/
theorem tensorEvaluation_bijective : Function.Bijective (tensorEvaluation L K) := by
  have hd : Module.finrank K (K ⊗[ℚ] L) = Module.finrank K (K × K) := by
    rw [Module.finrank_baseChange, IsQuadraticExtension.finrank_eq_two ℚ L,
      Module.finrank_prod, Module.finrank_self]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
    (tensorEvaluation_surjective L K), tensorEvaluation_surjective L K⟩

/-- The actual tensor algebra splits through the natural and conjugate characters. -/
def tensorEquiv : K ⊗[ℚ] L ≃ₐ[K] K × K :=
  AlgEquiv.ofBijective (tensorEvaluation L K) (tensorEvaluation_bijective L K)

@[simp]
theorem tensorEquiv_tmul (k : K) (r : L) :
    tensorEquiv L K (k ⊗ₜ[ℚ] r) =
      (k * algebraMap L K r, k * algebraMap L K (IsCMField.complexConj L r)) := rfl

variable (R : Type w) [CommRing R] [Algebra K R] [Algebra ℚ R]
  [IsScalarTower ℚ K R]

/-- The splitting after arbitrary scalar extension, including nonreduced coefficient rings. -/
def algebraEquiv : R ⊗[ℚ] L ≃ₐ[R] R × R :=
  ((Algebra.TensorProduct.cancelBaseChange ℚ K R R L).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) (tensorEquiv L K))).trans
    ((Algebra.TensorProduct.prodRight K R R K K).trans
      (AlgEquiv.prodCongr (Algebra.TensorProduct.rid K R R)
        (Algebra.TensorProduct.rid K R R)))

@[simp]
theorem algebraEquiv_tmul (r : R) (t : L) :
    algebraEquiv L K R (r ⊗ₜ[ℚ] t) =
      (r * algebraMap K R (algebraMap L K t),
        r * algebraMap K R (algebraMap L K (IsCMField.complexConj L t))) := by
  simp [algebraEquiv, Algebra.TensorProduct.prodRight_tmul, Algebra.smul_def, mul_comm]

end Langlands.Shimura.ImaginaryQuadratic
