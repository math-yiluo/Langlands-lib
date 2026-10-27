import Langlands.Representation.Shahidi.JacquetDiagonalStatement
import Langlands.Representation.Shahidi.JacquetRadicalProof

/-! # Scalar Jacquet covariance under exchanged unipotent diagonal blocks -/

noncomputable section

namespace Langlands.Shahidi

open GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

section Algebra

variable {F : Type uF} [Field F] {m n : ℕ}

/-- The last row of an upper-unipotent matrix fixes every rectangular matrix. -/
theorem upperUnipotent_mul_rectangular_last (u : upperUnipotent (n + 1) F)
    (x : Matrix (Fin (n + 1)) (Fin (m + 1)) F) (j : Fin (m + 1)) :
    (u.val.val * x) (Fin.last n) j = x (Fin.last n) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro i _ hi
    rw [UpperUnipotent.entry_eq_zero u (lt_of_le_of_ne (Fin.le_last i) hi), zero_mul]
  · simp

/-- The first column of an upper-unipotent matrix fixes every rectangular matrix. -/
theorem rectangular_mul_upperUnipotent_zero (u : upperUnipotent (m + 1) F)
    (x : Matrix (Fin (n + 1)) (Fin (m + 1)) F) (i : Fin (n + 1)) :
    (x * u.val.val) i 0 = x i 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    rw [UpperUnipotent.entry_eq_zero u (lt_of_le_of_ne (Fin.zero_le j) (Ne.symm hj)),
      mul_zero]
  · simp

variable [TopologicalSpace F] (ψ : UnitaryAdditiveCharacter F)

/-- The negative-corner Jacquet kernel is fixed by the exchanged unipotent Levi. -/
theorem intertwiningJacquetKernel_unipotent_conj
    (u₁ : upperUnipotent (m + 1) F) (u₂ : upperUnipotent (n + 1) F)
    (x : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    intertwiningJacquetKernel m n ψ ((u₂⁻¹).val.val * x * u₁.val.val) =
      intertwiningJacquetKernel m n ψ x := by
  rw [intertwiningJacquetKernel_eq_neg_corner, intertwiningJacquetKernel_eq_neg_corner,
    rectangular_mul_upperUnipotent_zero, upperUnipotent_mul_rectangular_last]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ℓ : V →ₗ[ℂ] ℂ)

/-- Scalar left covariance gives the actual right-translate integrand identity. -/
theorem jacquetIntegrand_rightTranslate_unipotent_blockSum
    (u₁ : upperUnipotent (m + 1) F) (u₂ : upperUnipotent (n + 1) F) (z : ℂ)
    (f : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V)
    (hf : ∀ g, ℓ (f (blockSum (u₁.val, u₂.val) * g)) = z * ℓ (f g))
    (x : Matrix (Fin (n + 1)) (Fin (m + 1)) F) :
    jacquetIntegrand m n ψ ℓ
        (fun g => f (g * swapRank (m + 1) (n + 1) F
          (blockSum (u₂.val, u₁.val)))) x =
      z * jacquetIntegrand m n ψ ℓ f ((u₂⁻¹).val.val * x * u₁.val.val) := by
  have hpt :
      blockWeyl (m + 1) (n + 1) F * intertwiningUnipotent (m + 1) (n + 1) F x *
          swapRank (m + 1) (n + 1) F (blockSum (u₂.val, u₁.val)) =
        blockSum (u₁.val, u₂.val) *
          (blockWeyl (m + 1) (n + 1) F *
            intertwiningUnipotent (m + 1) (n + 1) F
              ((u₂⁻¹).val.val * x * u₁.val.val)) := by
    rw [intertwiningUnipotent, intertwiningUnipotent, mul_assoc, ← map_mul,
      upper_mul_blockSum, map_mul, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [← blockWeyl_conjugate_blockSum (m + 1) (n + 1) F u₂.val u₁.val,
      inv_mul_cancel_right]
  simp only [jacquetIntegrand_apply]
  rw [hpt, hf, intertwiningJacquetKernel_unipotent_conj]
  ring

end Algebra

section Integral

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
variable [MeasurableAdd₂ F] [MeasurableMul F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {m n : ℕ}
variable (ψ : UnitaryAdditiveCharacter F) (ℓ : V →ₗ[ℂ] ℂ)
variable (μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))

/-- Measure-preserving unipotent diagonal changes preserve the integrable domain. -/
theorem integrable_jacquetIntegrand_rightTranslate_unipotent_blockSum
    (u₁ : upperUnipotent (m + 1) F) (u₂ : upperUnipotent (n + 1) F) (z : ℂ)
    (f : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V)
    (hf : ∀ g, ℓ (f (blockSum (u₁.val, u₂.val) * g)) = z * ℓ (f g))
    (hμ : μ.map (rectangularConj u₂.val u₁.val) = μ)
    (hi : Integrable (jacquetIntegrand m n ψ ℓ f) μ) :
    Integrable (jacquetIntegrand m n ψ ℓ
      (fun g => f (g * swapRank (m + 1) (n + 1) F
        (blockSum (u₂.val, u₁.val))))) μ := by
  have hmap : Integrable (jacquetIntegrand m n ψ ℓ f)
      (μ.map (rectangularConj u₂.val u₁.val)) := by
    rw [hμ]
    exact hi
  have hc := (integrable_map_equiv (rectangularConj u₂.val u₁.val) _).1 hmap
  have hfun := funext (jacquetIntegrand_rightTranslate_unipotent_blockSum ψ ℓ u₁ u₂ z f hf)
  rw [hfun]
  exact hc.const_mul z

/-- Ordinary scalar integration transforms by the same unipotent diagonal scalar. -/
theorem integral_jacquetIntegrand_rightTranslate_unipotent_blockSum
    (u₁ : upperUnipotent (m + 1) F) (u₂ : upperUnipotent (n + 1) F) (z : ℂ)
    (f : Langlands.GeneralLinear (m + 1 + (n + 1)) F → V)
    (hf : ∀ g, ℓ (f (blockSum (u₁.val, u₂.val) * g)) = z * ℓ (f g))
    (hμ : μ.map (rectangularConj u₂.val u₁.val) = μ) :
    (∫ x, jacquetIntegrand m n ψ ℓ
        (fun g => f (g * swapRank (m + 1) (n + 1) F
          (blockSum (u₂.val, u₁.val)))) x ∂μ) =
      z * ∫ x, jacquetIntegrand m n ψ ℓ f x ∂μ := by
  simp_rw [jacquetIntegrand_rightTranslate_unipotent_blockSum ψ ℓ u₁ u₂ z f hf]
  rw [integral_const_mul]
  congr 1
  change (∫ x, jacquetIntegrand m n ψ ℓ f (rectangularConj u₂.val u₁.val x) ∂μ) = _
  rw [← integral_map_equiv (rectangularConj u₂.val u₁.val), hμ]

end Integral

/-- The closed scalar unipotent diagonal prerequisite for the JPSS construction. -/
theorem jacquetDiagonalCovariance : JacquetDiagonalCovarianceStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro V _ _ ψ m n ℓ μ _ u₁ u₂ z f hf
  have hnorm (r : ℕ) (u : upperUnipotent r F.Carrier) :
      T.determinantNorm r u.val = 1 := by
    have hd : GeneralLinear.determinant u.val = 1 :=
      Units.ext (RankinSelberg.unipotent_det u)
    change T.normalizedAbsUnits (GeneralLinear.determinant u.val) = 1
    rw [hd, map_one]
  have hμ : μ.map (rectangularConj u₂.val u₁.val) = μ := by
    simpa only [hnorm, Units.val_one, one_pow, div_one, one_smul] using
      (map_rectangularConj_padic F T μ u₂.val u₁.val)
  refine ⟨hμ, ?_, ?_⟩
  · intro x
    exact jacquetIntegrand_rightTranslate_unipotent_blockSum ψ ℓ u₁ u₂ z f hf x
  · intro hi
    exact ⟨integrable_jacquetIntegrand_rightTranslate_unipotent_blockSum
        ψ ℓ μ u₁ u₂ z f hf hμ hi,
      integral_jacquetIntegrand_rightTranslate_unipotent_blockSum ψ ℓ μ u₁ u₂ z f hf hμ⟩

end Langlands.Shahidi
