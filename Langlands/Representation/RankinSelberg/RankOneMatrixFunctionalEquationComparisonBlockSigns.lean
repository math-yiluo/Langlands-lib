import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylSigns
import Langlands.Representation.RankinSelberg.RankOneQuotient

/-! Coordinate sign changes on the actual rank-one JPSS block matrices. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open GeneralLinear Whittaker MeasureTheory MeasureTheory.Measure HarmonicAnalysis QuotientIntegration
open AdjacentBlockReduction

universe uK

variable {K : Type uK} [Field K]

/-- Alternating row signs on the actual rectangular variable. -/
def rankOneBlockSigns (j : ℕ) (X : Matrix (Fin j) (Fin 1) K) :
    Matrix (Fin j) (Fin 1) K :=
  fun i b => (-1 : K) ^ (i.val + 1) * X i b

@[simp] theorem rankOneBlockSigns_apply (j : ℕ)
    (X : Matrix (Fin j) (Fin 1) K) (i : Fin j) (b : Fin 1) :
    rankOneBlockSigns j X i b = (-1 : K) ^ (i.val + 1) * X i b := rfl

private theorem sign_mul_self (d : ℕ) : (-1 : K) ^ d * (-1 : K) ^ d = 1 := by
  rw [← mul_pow]
  simp

private theorem alternating_sign_product (n : ℕ) (i : Fin (n + 1)) :
    (-1 : K) ^ (n - i.val) * (-1 : K) ^ n = (-1 : K) ^ i.val := by
  have hp : (-1 : K) ^ n = (-1 : K) ^ (n - i.val) * (-1 : K) ^ i.val := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)]
  rw [hp, ← mul_assoc, sign_mul_self, one_mul]

/-- Right multiplication by the leading sign negates both the scalar and
the rectangular first-column variable in the actual block matrix. -/
theorem blockMatrixAt_rankOne_mul_leadingSign {n : ℕ} (j k : ℕ)
    (hr : n = 0 + (j + k + 1)) (g : Langlands.GeneralLinear (0 + 1) K)
    (X : Matrix (Fin j) (Fin (0 + 1)) K) :
    blockMatrixAt j k hr g X * rankOneWeylLeadingSign n =
      blockMatrixAt j k hr (-g) (-X) := by
  apply Units.ext
  ext i b
  change ((blockMatrixAt j k hr g X).val * (rankOneWeylLeadingSign (K := K) n).val) i b = _
  rw [rankOneWeylLeadingSign_val, Matrix.mul_diagonal]
  simp only [blockMatrixAt_entry, Units.val_neg, Matrix.neg_apply]
  by_cases hb : b = 0
  · subst b
    by_cases hi : i.val < 0 + 1
    · have hie : i = 0 := by apply Fin.ext; simp only [Fin.val_zero]; omega
      subst i
      simp
    · have hine : i ≠ 0 := by intro h; subst i; simp at hi
      simp only [hi, dite_false, hine, ite_false, Fin.val_zero, Nat.zero_lt_succ,
        dite_true, zero_add, ite_true, mul_neg_one]
      split_ifs <;> simp
  · have hbv : ¬b.val < 0 + 1 := by
      have h := Fin.pos_of_ne_zero hb
      omega
    simp [hb, hbv]

/-- Alternating conjugation fixes the leading scalar and introduces exactly
the alternating row signs in the actual block matrix. -/
theorem alternating_blockMatrixAt_rankOne {n : ℕ} (j k : ℕ)
    (hr : n = 0 + (j + k + 1)) (g : Langlands.GeneralLinear (0 + 1) K)
    (X : Matrix (Fin j) (Fin (0 + 1)) K) :
    rankOneWeylAlternating n * blockMatrixAt j k hr g X * rankOneWeylAlternating n =
      blockMatrixAt j k hr g (rankOneBlockSigns j X) := by
  apply Units.ext
  ext i b
  change (((rankOneWeylAlternating (K := K) n).val * (blockMatrixAt j k hr g X).val) *
    (rankOneWeylAlternating (K := K) n).val) i b = _
  rw [rankOneWeylAlternating_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [blockMatrixAt_entry, rankOneBlockSigns_apply]
  by_cases hb : b = 0
  · subst b
    by_cases hi : i.val < 0 + 1
    · have hie : i = 0 := by apply Fin.ext; simp only [Fin.val_zero]; omega
      subst i
      simp
      calc
        _ = ((-1 : K) ^ n * (-1 : K) ^ n) * g 0 0 := by ring
        _ = _ := by rw [sign_mul_self, one_mul]
    · have hine : i ≠ 0 := by intro h; subst i; simp at hi
      simp only [hi, dite_false, hine, ite_false, Fin.val_zero, Nat.sub_zero,
        Nat.zero_lt_succ, dite_true, zero_add]
      by_cases hx : 0 + 1 ≤ i.val ∧ i.val < 0 + 1 + j
      · simp only [hx.1, hx.2, and_self, dite_true]
        have he : i.val - (0 + 1) + 1 = i.val := by omega
        rw [he]
        have hX (a : Fin j) (b : Fin (0 + 1)) : X a b = X a 0 := by
          apply congrArg (X a)
          apply Fin.ext
          simp only [Fin.val_zero]
          omega
        simp only [hX]
        calc
          _ = ((-1 : K) ^ (n - i.val) * (-1 : K) ^ n) *
              X ⟨i.val - (0 + 1), by omega⟩ 0 := by ring
          _ = _ := by rw [alternating_sign_product]
      · simp [hx]
  · have hbv : ¬b.val < 0 + 1 := by
      have h := Fin.pos_of_ne_zero hb
      omega
    simp only [hbv, dite_false]
    by_cases hi : i.val < 0 + 1
    · simp [hi]
    · simp only [hi, dite_false]
      by_cases hib : i = b
      · subst b
        simp [sign_mul_self]
      · simp [hib]

/-- The alternating row substitution is its own inverse. -/
theorem rankOneBlockSigns_involutive (j : ℕ) :
    Function.Involutive (rankOneBlockSigns (K := K) j) := by
  intro X
  funext i b
  simp only [rankOneBlockSigns_apply, ← mul_assoc, sign_mul_self, one_mul]

section Topology

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- The actual quotient sign map is right translation by the scalar `-1`. -/
def rankOneQuotientSign :
    LeftQuotient (GeneralLinear.upperUnipotent 1 K) ≃ₜ
      LeftQuotient (GeneralLinear.upperUnipotent 1 K) :=
  rightTranslate (GeneralLinear.upperUnipotent 1 K) (-1)

@[simp] theorem rankOneQuotientSign_mk (g : Langlands.GeneralLinear 1 K) :
    rankOneQuotientSign (Quotient.mk _ g) = Quotient.mk _ (-g) := by
  simp only [rankOneQuotientSign, rightTranslate_mk, mul_neg_one]

end Topology

section Measures

variable [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [LocallyCompactSpace K] [T2Space K]

/-- The alternating row substitution as a measurable involution. -/
def rankOneBlockSignsMeasurableEquiv (j : ℕ) :
    Matrix (Fin j) (Fin 1) K ≃ᵐ Matrix (Fin j) (Fin 1) K where
  toFun := rankOneBlockSigns j
  invFun := rankOneBlockSigns j
  left_inv := rankOneBlockSigns_involutive j
  right_inv := rankOneBlockSigns_involutive j
  measurable_toFun := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro b
    exact measurable_const.mul ((measurable_pi_apply b).comp (measurable_pi_apply i))
  measurable_invFun := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro b
    exact measurable_const.mul ((measurable_pi_apply b).comp (measurable_pi_apply i))

private theorem scalarSign_preserving (ν : AdditiveHaarMeasure K) (d : ℕ) :
    MeasurePreserving (fun x : K => (-1 : K) ^ d * x) ν.measure ν.measure := by
  rcases neg_one_pow_eq_or K d with h | h
  · convert! MeasurePreserving.id ν.measure using 1
    funext x
    simp [h]
  · simpa only [h, neg_one_mul] using measurePreserving_neg ν.measure

/-- Alternating row signs preserve the exact rectangular measure formed
from the supplied additive Haar measure. -/
theorem rankOneBlockSigns_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (j : ℕ) :
    MeasurePreserving (rankOneBlockSigns (K := K) j)
      (rectangularMeasure ν j 1) (rectangularMeasure ν j 1) := by
  exact measurePreserving_pi (fun _ : Fin j => rowMeasure ν 1)
    (fun _ : Fin j => rowMeasure ν 1) (fun i =>
      measurePreserving_pi (fun _ : Fin 1 => ν.measure) (fun _ : Fin 1 => ν.measure)
        (fun _ => scalarSign_preserving ν (i.val + 1)))

/-- Negation preserves the supplied rectangular measure, with no rescaling. -/
theorem rankOneRectangularNeg_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (j : ℕ) :
    MeasurePreserving (fun X : Matrix (Fin j) (Fin 1) K => -X)
      (rectangularMeasure ν j 1) (rectangularMeasure ν j 1) := by
  exact measurePreserving_pi (fun _ : Fin j => rowMeasure ν 1)
    (fun _ : Fin j => rowMeasure ν 1) (fun _ =>
      measurePreserving_pi (fun _ : Fin 1 => ν.measure) (fun _ : Fin 1 => ν.measure)
        (fun _ => measurePreserving_neg ν.measure))

/-- The alternating substitution is valid for the total complex integral. -/
theorem integral_rankOneBlockSigns (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (j : ℕ) (f : Matrix (Fin j) (Fin 1) K → ℂ) :
    (∫ X, f (rankOneBlockSigns j X) ∂rectangularMeasure ν j 1) =
      ∫ X, f X ∂rectangularMeasure ν j 1 :=
  (rankOneBlockSigns_preserving ν j).integral_comp
    (rankOneBlockSignsMeasurableEquiv j).measurableEmbedding f

variable [MeasurableSpace (Langlands.GeneralLinear 1 K)]
  [BorelSpace (Langlands.GeneralLinear 1 K)]
  [MeasurableSpace (GeneralLinear.upperUnipotent 1 K)]
  [BorelSpace (GeneralLinear.upperUnipotent 1 K)]
  [MeasurableSpace (LeftQuotient (GeneralLinear.upperUnipotent 1 K))]
  [BorelSpace (LeftQuotient (GeneralLinear.upperUnipotent 1 K))]

omit [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [LocallyCompactSpace K] [T2Space K] [BorelSpace (Langlands.GeneralLinear 1 K)]
  [BorelSpace (LeftQuotient (GeneralLinear.upperUnipotent 1 K))] in
/-- Every supplied compatible quotient measure is preserved by the scalar
sign substitution. -/
theorem rankOneQuotientSign_preserving
    (μG : Measure (Langlands.GeneralLinear 1 K))
    (μN : Measure (GeneralLinear.upperUnipotent 1 K)) [IsMulRightInvariant μN]
    (μ : Measure (LeftQuotient (GeneralLinear.upperUnipotent 1 K)))
    (hμ : IsCompatible (GeneralLinear.upperUnipotent 1 K) μG μN μ) :
    MeasurePreserving (rankOneQuotientSign (K := K)) μ μ :=
  hμ.right_invariant (-1)

omit [BorelSpace (Langlands.GeneralLinear 1 K)]
  [BorelSpace (LeftQuotient (GeneralLinear.upperUnipotent 1 K))] in
/-- The simultaneous scalar/rectangular negation in `m_j(g,X) E` preserves
the exact product of any compatible quotient measure and the supplied Haar. -/
theorem rankOneBlockNeg_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (j : ℕ)
    (μG : Measure (Langlands.GeneralLinear 1 K))
    (μN : Measure (GeneralLinear.upperUnipotent 1 K)) [IsMulRightInvariant μN]
    (μ : Measure (LeftQuotient (GeneralLinear.upperUnipotent 1 K))) [SFinite μ]
    (hμ : IsCompatible (GeneralLinear.upperUnipotent 1 K) μG μN μ) :
    MeasurePreserving
      (fun z : LeftQuotient (GeneralLinear.upperUnipotent 1 K) ×
        Matrix (Fin j) (Fin 1) K => (rankOneQuotientSign z.1, -z.2))
      (μ.prod (rectangularMeasure ν j 1)) (μ.prod (rectangularMeasure ν j 1)) :=
  (rankOneQuotientSign_preserving μG μN μ hμ).prod
    (rankOneRectangularNeg_preserving ν j)

end Measures

end Langlands.RankinSelberg
