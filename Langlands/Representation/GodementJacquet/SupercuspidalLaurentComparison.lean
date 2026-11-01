import Langlands.Representation.GodementJacquet.SupercuspidalOperatorComparison

/-! # Laurent dependence of a Fourier-regular scalar comparison -/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance laurentComparisonTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance laurentComparisonValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance laurentComparisonLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance laurentComparisonT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance laurentComparisonDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance laurentComparisonMeasurable : MeasurableSpace F.Carrier := borel _
local instance laurentComparisonBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance laurentComparisonGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance laurentComparisonGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-- The reflected exponent uses the negative determinant order. -/
theorem determinantWeight_sub_spectral
    (g : GeneralLinear (n + 1) F.Carrier) (t s : ℂ) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g (t - s) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g t *
        spectralPoint F.canonicalTopologicalData.residueCardinality s ^
          (-F.canonicalTopologicalData.ord (Matrix.det g.val)) := by
  rw [show t - s = -s + t by ring, determinantWeight_shift_spectral]
  congr 1
  rw [show spectralPoint F.canonicalTopologicalData.residueCardinality (-s) =
      (spectralPoint F.canonicalTopologicalData.residueCardinality s)⁻¹ by
        simp only [spectralPoint, neg_neg, Complex.cpow_neg, inv_inv], inv_zpow, zpow_neg]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Every algebraic evaluation of a regular-test operator at a reflected
parameter is one Laurent polynomial at the original spectral point. -/
theorem exists_laurent_regularMatrixZetaOperator_dual_sub
    (σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (t : ℂ)
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1))
    (v : V) (ℓ : Module.Dual ℂ V) :
    ∃ A : LaurentCoefficients, ∀ s : ℂ,
      ℓ (regularMatrixZetaOperator F σ hσ (t - s) Φ v) =
        laurentEval (spectralUnit
          (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one) s) A := by
  let T := F.canonicalTopologicalData
  let ord : GeneralLinear (n + 1) F.Carrier → ℤ :=
    fun g => -T.ord (Matrix.det g.val)
  have hord : Continuous ord :=
    ((continuous_ord_units T).comp (T.generalLinearDeterminant (n + 1)).continuous).neg
  let h : GeneralLinear (n + 1) F.Carrier → ℂ := fun g =>
    Φ.val g.val * ℓ (σ g v) * determinantWeight (normalizedAbsoluteValue T) g t
  have hh : Continuous h :=
    ((Φ.val.continuous.comp Units.continuous_val).mul
      (((Hecke.orbitMap_locallyConstant σ (hσ v)).comp ℓ).continuous)).mul
      (determinantWeight_locallyConstant F t).continuous
  have hc : HasCompactSupport h :=
    ((hasCompactSupport_restrict_of_mem_regularMatrixTests (n + 1) Φ.property).mul_right).mul_right
  obtain ⟨A, hA⟩ := exists_laurent_integral_discreteWeight
    (generalLinearHaar F.Carrier n) T.residueCardinality
    (Nat.zero_lt_one.trans T.residueCardinality_gt_one) ord hord h hh hc
  refine ⟨A, fun s => ?_⟩
  rw [regularMatrixZetaOperator_dual]
  change (∫ g, Φ.val g.val * ℓ (σ g v) *
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g (t - s)
      ∂generalLinearHaar F.Carrier n) = _
  simp_rw [determinantWeight_sub_spectral F]
  simpa only [h, ord, T, mul_assoc] using (hA s).2

/-- The Laurent polynomial of one algebraic operator evaluation at a reflected
exponent, chosen from the actual finite determinant-order integral. -/
def regularMatrixZetaEvaluationLaurent
    (σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (t : ℂ)
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1))
    (v : V) (ℓ : Module.Dual ℂ V) : LaurentCoefficients :=
  Classical.choose (exists_laurent_regularMatrixZetaOperator_dual_sub F σ hσ t Φ v ℓ)

theorem regularMatrixZetaEvaluationLaurent_spec
    (σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (t : ℂ)
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1))
    (v : V) (ℓ : Module.Dual ℂ V) (s : ℂ) :
    ℓ (regularMatrixZetaOperator F σ hσ (t - s) Φ v) =
      laurentEval (spectralUnit
        (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one) s)
        (regularMatrixZetaEvaluationLaurent F σ hσ t Φ v ℓ) :=
  Classical.choose_spec (exists_laurent_regularMatrixZetaOperator_dual_sub F σ hσ t Φ v ℓ) s

variable {m : ℕ}

/-- A pointwise scalar comparison with reflected Fourier integrals has one
Laurent scalar valid simultaneously for all tests and all parameters. -/
theorem exists_laurent_scalar_of_fourierRegular_cross
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (σ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hσ : IsSmooth σ)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (t : ℂ)
    (hcross : ∀ (s : ℂ) (Φ Ψ : fourierRegularMatrixTests (m + 1) ψ ν hsd),
      fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ *
          regularMatrixZetaOperator F σ hσ (t - s)
            ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Ψ.val, Ψ.property.2⟩ =
        regularMatrixZetaOperator F σ hσ (t - s)
            ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ *
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Ψ) :
    ∃ A : LaurentCoefficients, ∀ (s : ℂ)
      (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd),
      regularMatrixZetaOperator F σ hσ (t - s)
          ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ =
        laurentEval (spectralUnit
          (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one) s) A •
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ := by
  let := hi
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (m + 1) F.Carrier)) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨Φ₀, u, hu, hΦ₀⟩ :=
    exists_fourierRegular_constant_output F hm ρ hρ ψ ν hsd v hv
  obtain ⟨ℓ, _, hℓ⟩ := exists_smoothFunctional_ne_zero F ρ hρ.1.1 u hu
  obtain ⟨B, hB⟩ := exists_laurent_regularMatrixZetaOperator_dual_sub F σ hσ t
    ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ₀.val, Φ₀.property.2⟩ v ℓ
  refine ⟨(ℓ u)⁻¹ • B, fun s => ?_⟩
  obtain ⟨c, hc⟩ := exists_scalar_of_fourierRegularMatrixZetaOperator_cross
    F hm ρ hρ hi ψ ν hsd s
    (fun Φ => regularMatrixZetaOperator F σ hσ (t - s)
      ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩) (hcross s)
  have he := congrArg (fun L : Module.End ℂ V => ℓ (L v)) (hc Φ₀)
  simp only [LinearMap.smul_apply, map_smul, fourierRegularMatrixZetaOperator_apply,
    hΦ₀ s, smul_eq_mul, hB s] at he
  have heval : laurentEval (spectralUnit
      (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one) s)
      ((ℓ u)⁻¹ • B) = c := by
    rw [laurentEval_smul, he]
    rw [mul_comm c (ℓ u), inv_mul_cancel_left₀ hℓ]
  intro Φ
  rw [heval]
  exact hc Φ

end Langlands.GodementJacquet.Padic
