import Langlands.Representation.GodementJacquet.TateScalarTransport
import Langlands.Representation.GodementJacquet.TateScalarMellin
import Langlands.Representation.GodementJacquet.TateCharacterShells
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonScalarHaar
import Langlands.LocalFactor.Abelian.Padic

/-! Exact normalization between additive Tate zeta and multiplicative Mellin integrals. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
private local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
private local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
private local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
private local instance : MeasurableSpace F.Carrier := borel _
private local instance : BorelSpace F.Carrier := ⟨rfl⟩
private local instance : MeasurableSpace F.Carrierˣ := borel _
private local instance : BorelSpace F.Carrierˣ := ⟨rfl⟩
private local instance : MeasurableSpace (Langlands.GeneralLinear 1 F.Carrier) := borel _
private local instance : BorelSpace (Langlands.GeneralLinear 1 F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "abv" => normalizedAbsoluteValue T
local notation "U" => LocalFactor.PadicAbelian.integralUnits T

private theorem scalar_entry (a : F.Carrierˣ) :
    (tateScalarEquiv F.Carrier a) 0 0 = (a : F.Carrier) := by
  simp [tateScalarEquiv, scalar, Matrix.GeneralLinearGroup.coe_scalar]

private theorem scalar_det (a : F.Carrierˣ) :
    (tateScalarEquiv F.Carrier a).val.det = (a : F.Carrier) := by
  exact congrArg Units.val ((tateScalarEquiv F.Carrier).symm_apply_apply a)

/-- The natural GL density weight becomes the normalized scalar absolute value. -/
theorem tateScalarEquiv_natWeight (a : F.Carrierˣ) :
    determinantWeight abv (tateScalarEquiv F.Carrier a) 1 =
      (F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℂ) := by
  rw [determinantWeight, scalar_det]
  exact Complex.cpow_one _

private theorem unit_indicator_weight (a : F.Carrierˣ) :
    determinantWeight abv (tateScalarEquiv F.Carrier a) 1 *
        (LocalFactor.PadicAbelian.integralUnits F.canonicalTopologicalData).indicator
          (fun _ => (1 : ℂ)) ((tateScalarEquiv F.Carrier a) 0 0) =
      (RankinSelberg.integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ).indicator (fun _ => (1 : ℂ)) a := by
  classical
  rw [scalar_entry, tateScalarEquiv_natWeight]
  have hmem : (a : F.Carrier) ∈ U ↔ a ∈ RankinSelberg.integralUnits (ValuativeRel.valuation F.Carrier).integer := by
    change ((a : F.Carrier) ≠ 0 ∧
      F.canonicalTopologicalData.ord (a : F.Carrier) = 0) ↔ _
    rw [mem_integralUnits_iff_ord_zero F T a]
    exact ⟨fun h => h.2, fun h => ⟨a.ne_zero, h⟩⟩
  by_cases ha : a ∈ RankinSelberg.integralUnits (ValuativeRel.valuation F.Carrier).integer
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hmem.mpr ha)]
    have habs : F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) = 1 :=
      (F.canonicalTopologicalData.ord_eq_zero_iff_normalizedAbs a).mp
        ((mem_integralUnits_iff_ord_zero F T a).mp ha)
    simp [habs]
  · rw [Set.indicator_of_notMem ha,
      Set.indicator_of_notMem (fun h => ha (hmem.mp h)), mul_zero]

/-- The fixed scalar in determinant-density cancellation is exactly the
additive Haar mass of the integral units. -/
theorem rectangularHaarScalar_rankOne_eq_unitMass
    (ν : AdditiveHaarMeasure F.Carrier) :
    (GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) =
      (ν.measure U).toReal := by
  classical
  have hK : MeasurableSet (RankinSelberg.integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ) :=
    (integralUnits_isOpen _ Valuation.isOpen_integer).measurableSet
  have hU : MeasurableSet U := by
    have hUeq : U = Units.val '' (RankinSelberg.integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ) := by
      ext x
      constructor
      · rintro ⟨hx, ho⟩
        exact ⟨Units.mk0 x hx,
          (mem_integralUnits_iff_ord_zero F T _).mpr ho, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.ne_zero, (mem_integralUnits_iff_ord_zero F T a).mp ha⟩
    rw [hUeq]
    exact (IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _
      (integralUnits_isOpen _ Valuation.isOpen_integer)).measurableSet
  have h := integral_generalLinear_one_natWeight F ν
    ((LocalFactor.PadicAbelian.integralUnits F.canonicalTopologicalData).indicator
      (fun _ => (1 : ℂ)))
  rw [← integral_tateScalarEquiv F] at h
  simp_rw [unit_indicator_weight F] at h
  rw [integral_indicator_const _ hK, integral_indicator_const _ hU] at h
  simp only [measureReal_def, localMultiplicativeHaar_integerUnits, ENNReal.toReal_one,
    one_smul, mul_one, Complex.real_smul] at h
  have hc : ((GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (GLDeterminantDensity.rectangularHaarScalar_pos F ν 0).ne'
  have he : ((GLDeterminantDensity.rectangularHaarScalar F ν 0 : ℝ) : ℂ) =
      ((ν.measure U).toReal : ℂ) := by
    calc
      _ = _ * 1 := (mul_one _).symm
      _ = _ * (_⁻¹ * ((ν.measure U).toReal : ℂ)) := by rw [← h]
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  exact_mod_cast he

/-- Positivity is inherited from the actual determinant-density Haar comparison. -/
theorem tate_integralUnits_mass_pos (ν : AdditiveHaarMeasure F.Carrier) :
    0 < (ν.measure U).toReal := by
  rw [← rectangularHaarScalar_rankOne_eq_unitMass F ν]
  exact_mod_cast GLDeterminantDensity.rectangularHaarScalar_pos F ν 0

private theorem real_mul_exp_sub_one (r : ℝ) (hr : 0 < r) (s : ℂ) :
    (r : ℂ) * Complex.exp ((s - 1) * (Real.log r : ℂ)) = (r : ℂ) ^ s := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    ← Complex.ofReal_log hr.le]
  conv_lhs =>
    lhs
    rw [← Real.exp_log hr, Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Multiplying the additive integrand by the density-cancelling absolute
value gives the original Mellin integrand at every nonzero scalar. -/
theorem tate_zetaIntegrand_weight (χ : Quasicharacter F.Carrier)
    (Φ : SchwartzBruhat F.Carrier) (s : ℂ) (a : F.Carrierˣ) :
    determinantWeight abv (tateScalarEquiv F.Carrier a) 1 *
        LocalFactor.PadicAbelian.zetaIntegrand T Φ χ s
          ((tateScalarEquiv F.Carrier a) 0 0) =
      scalarMellinIntegrand F.canonicalTopologicalData.normalizedAbs
        (fun a => (χ a : ℂ)) 1 Φ s a := by
  rw [scalar_entry, tateScalarEquiv_natWeight]
  simp only [LocalFactor.PadicAbelian.zetaIntegrand, ite_eq_right a.ne_zero,
    LocalFactor.PadicAbelian.characterExtension, dite_eq_right a.ne_zero,
    Units.mk0_val, scalarMellinIntegrand, Nat.cast_one, one_mul]
  have hr : 0 < F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) :=
    (F.canonicalTopologicalData.normalizedAbs_of_ne_zero a.ne_zero) ▸
      zpow_pos (by exact_mod_cast
        (lt_trans Nat.zero_lt_one F.canonicalTopologicalData.residueCardinality_gt_one)) _
  rw [← real_mul_exp_sub_one _ hr s]
  ring

/-- Genuine convergence agrees for the two actual integral conventions. -/
theorem scalarMellinIntegrable_iff_zetaIntegrable
    (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier)
    (Φ : SchwartzBruhat F.Carrier) (s : ℂ) :
    Integrable (scalarMellinIntegrand F.canonicalTopologicalData.normalizedAbs
      (fun a => (χ a : ℂ)) 1 Φ s)
        (localMultiplicativeHaar F.Carrier) ↔
      Integrable (LocalFactor.PadicAbelian.zetaIntegrand T Φ χ s) ν.measure := by
  have h := integrable_generalLinear_one_natWeight_iff F ν
    (LocalFactor.PadicAbelian.zetaIntegrand T Φ χ s)
  rw [← integrable_tateScalarEquiv_iff F] at h
  simpa only [tate_zetaIntegrand_weight F χ Φ s] using h

/-- The exact conversion factor is the inverse additive Haar mass of the
integral units; the identity also respects totalized Bochner integrals. -/
theorem scalarMellinIntegral_eq_zeta
    (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier)
    (Φ : SchwartzBruhat F.Carrier) (s : ℂ) :
    scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs
        (localMultiplicativeHaar F.Carrier)
        (fun a => (χ a : ℂ)) 1 Φ s =
      ((ν.measure U).toReal : ℂ)⁻¹ *
        LocalFactor.PadicAbelian.zeta T ν.measure Φ χ s := by
  have h := integral_generalLinear_one_natWeight F ν
    (LocalFactor.PadicAbelian.zetaIntegrand T Φ χ s)
  rw [← integral_tateScalarEquiv F] at h
  simpa only [tate_zetaIntegrand_weight F χ Φ s, scalarMellinIntegral,
    LocalFactor.PadicAbelian.zeta, rectangularHaarScalar_rankOne_eq_unitMass F ν] using h

/-- Exact additive/multiplicative Tate integral comparison with every supplied
Haar measure, every character, every scalar test and every complex parameter. -/
def TateAdditiveMellinStatement : Prop :=
  ∀ (ν : AdditiveHaarMeasure F.Carrier),
    0 < (ν.measure U).toReal ∧
      ∀ (χ : Quasicharacter F.Carrier) (Φ : SchwartzBruhat F.Carrier) (s : ℂ),
        (Integrable (scalarMellinIntegrand F.canonicalTopologicalData.normalizedAbs
          (fun a => (χ a : ℂ)) 1 Φ s)
            (localMultiplicativeHaar F.Carrier) ↔
          Integrable (LocalFactor.PadicAbelian.zetaIntegrand T Φ χ s) ν.measure) ∧
        scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs
            (localMultiplicativeHaar F.Carrier)
            (fun a => (χ a : ℂ)) 1 Φ s =
          ((ν.measure U).toReal : ℂ)⁻¹ *
            LocalFactor.PadicAbelian.zeta T ν.measure Φ χ s

theorem tateAdditiveMellinStatement : TateAdditiveMellinStatement F := by
  intro ν
  exact ⟨tate_integralUnits_mass_pos F ν, fun χ Φ s =>
    ⟨scalarMellinIntegrable_iff_zetaIntegrable F ν χ Φ s,
      scalarMellinIntegral_eq_zeta F ν χ Φ s⟩⟩

end Langlands.GodementJacquet.Padic
