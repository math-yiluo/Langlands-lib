import Langlands.Representation.Shahidi.JacquetRadicalStatement
import Langlands.Representation.RankinSelberg.TwoBlockJacquetData

/-! # Boundary kernel and exchanged-radical covariance of the scalar Jacquet integral -/

noncomputable section

namespace Langlands.Shahidi

open HarmonicAnalysis MeasureTheory

universe uF uV

section Boundary

variable {F : Type uF} [Field F]

/-- Arithmetic rank transport preserves the superdiagonal sum. -/
theorem sum_superdiagonal_intertwiningUnipotent (m n : ℕ)
    (x : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    (∑ i : Fin (m + 1 + n),
      intertwiningUnipotent (m + 1) (n + 1) F x i.castSucc i.succ) =
      x (Fin.last n) 0 := by
  let e : Fin (m + 1 + n) ≃ Fin (n + 1 + m) := finCongr (by omega)
  have hsum :
      (∑ i : Fin (m + 1 + n),
        intertwiningUnipotent (m + 1) (n + 1) F x i.castSucc i.succ) =
      ∑ i : Fin (n + 1 + m), upper (n + 1) (m + 1) F x i.castSucc i.succ := by
    apply Fintype.sum_equiv e
    intro i
    change upper (n + 1) (m + 1) F x
        (Fin.cast (Nat.add_comm (m + 1) (n + 1)) i.castSucc)
        (Fin.cast (Nat.add_comm (m + 1) (n + 1)) i.succ) =
      upper (n + 1) (m + 1) F x (e i).castSucc (e i).succ
    congr 1
  rw [hsum, RankinSelberg.TwoBlockJacquet.sum_superdiagonal_upper]

variable [TopologicalSpace F] (ψ : UnitaryAdditiveCharacter F) (m n : ℕ)

/-- The positive character on the exchanged radical evaluates at its corner. -/
theorem intertwiningCharacter_eq_corner
    (x : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    (intertwiningCharacter m n ψ (Multiplicative.ofAdd x) : ℂ) =
      ψ.complex (x (Fin.last n) 0) := by
  rw [intertwiningCharacter_apply, sum_superdiagonal_intertwiningUnipotent]

/-- The conjugate character in the Jacquet integral has the negative corner. -/
theorem intertwiningJacquetKernel_eq_neg_corner
    (x : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    intertwiningJacquetKernel m n ψ x = ψ.complex (-(x (Fin.last n) 0)) := by
  rw [intertwiningJacquetKernel_eq_inv, intertwiningCharacter_eq_corner,
    AddChar.map_neg_eq_inv]

end Boundary

section Translation

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ψ : UnitaryAdditiveCharacter F) (m n : ℕ) (ℓ : V →ₗ[ℂ] ℂ)

/-- The kernel identity that compensates for a right translation of coordinates. -/
theorem intertwiningJacquetKernel_add_compensated
    (x y : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    intertwiningJacquetKernel m n ψ x =
      (intertwiningCharacter m n ψ (Multiplicative.ofAdd y) : ℂ) *
        intertwiningJacquetKernel m n ψ (x + y) := by
  rw [intertwiningJacquetKernel_eq_inv, intertwiningJacquetKernel_eq_inv]
  have hxy : Multiplicative.ofAdd (x + y) =
      Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl
  rw [hxy, map_mul, Units.val_mul, mul_inv_rev]
  rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]

/-- Pointwise covariance of the actual scalar Jacquet integrand. -/
theorem jacquetIntegrand_rightTranslate_intertwiningUnipotent
    (f : GeneralLinear (m + 1 + (n + 1)) F → V)
    (y x : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    jacquetIntegrand m n ψ ℓ
        (fun g => f (g * intertwiningUnipotent (m + 1) (n + 1) F y)) x =
      (intertwiningCharacter m n ψ (Multiplicative.ofAdd y) : ℂ) *
        jacquetIntegrand m n ψ ℓ f (x + y) := by
  simp only [jacquetIntegrand_apply, intertwiningUnipotent_add, ← mul_assoc]
  rw [intertwiningJacquetKernel_add_compensated ψ m n x y, mul_assoc]

variable [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F]
variable (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F)) [μ.IsAddRightInvariant]

/-- The ordinary integrable domain is preserved by exchanged-radical translation. -/
theorem integrable_jacquetIntegrand_rightTranslate_intertwiningUnipotent
    (f : GeneralLinear (m + 1 + (n + 1)) F → V)
    (y : Matrix (Fin (n + 1)) (Fin (m + 1)) F)
    (hf : Integrable (jacquetIntegrand m n ψ ℓ f) μ) :
    Integrable (jacquetIntegrand m n ψ ℓ
      (fun g => f (g * intertwiningUnipotent (m + 1) (n + 1) F y))) μ := by
  let : MeasurableAdd (Matrix (Fin (n + 1)) (Fin (m + 1)) F) :=
    inferInstanceAs (MeasurableAdd (Fin (n + 1) → Fin (m + 1) → F))
  have hfun := funext (jacquetIntegrand_rightTranslate_intertwiningUnipotent ψ m n ℓ f y)
  rw [hfun]
  exact (hf.comp_add_right y).const_mul _

/-- Right-invariant ordinary integration gives the positive character factor. -/
theorem integral_jacquetIntegrand_rightTranslate_intertwiningUnipotent
    (f : GeneralLinear (m + 1 + (n + 1)) F → V)
    (y : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    (∫ x, jacquetIntegrand m n ψ ℓ
        (fun g => f (g * intertwiningUnipotent (m + 1) (n + 1) F y)) x ∂μ) =
      (intertwiningCharacter m n ψ (Multiplicative.ofAdd y) : ℂ) *
        ∫ x, jacquetIntegrand m n ψ ℓ f x ∂μ := by
  let : MeasurableAdd (Matrix (Fin (n + 1)) (Fin (m + 1)) F) :=
    inferInstanceAs (MeasurableAdd (Fin (n + 1) → Fin (m + 1) → F))
  simp_rw [jacquetIntegrand_rightTranslate_intertwiningUnipotent ψ m n ℓ f y]
  rw [integral_const_mul, integral_add_right_eq_self]

end Translation

/-- The closed boundary and radical-covariance prerequisite for the JPSS construction. -/
theorem jacquetRadicalCovariance : JacquetRadicalCovarianceStatement.{uF, uV} := by
  constructor
  · intro F _ _ ψ m n x
    exact ⟨intertwiningCharacter_eq_corner ψ m n x,
      intertwiningJacquetKernel_eq_neg_corner ψ m n x⟩
  · intro F _ _ _ _ _ V _ _ ψ m n ℓ μ _ f y
    refine ⟨jacquetIntegrand_rightTranslate_intertwiningUnipotent ψ m n ℓ f y, ?_⟩
    intro hf
    exact ⟨integrable_jacquetIntegrand_rightTranslate_intertwiningUnipotent ψ m n ℓ μ f y hf,
      integral_jacquetIntegrand_rightTranslate_intertwiningUnipotent ψ m n ℓ μ f y⟩

end Langlands.Shahidi
