import Langlands.LocalFactor.AbelianDualityAdapter
import Langlands.LocalFactor.FourierDualHaarAdapter
import Langlands.LocalFactor.PadicAbelianStatement
import Langlands.LocalFactor.Abelian.Scaling

/-! # Scalar duality from the actual Tate local-analysis theorem -/

noncomputable section

universe uF uV

namespace Langlands.PadicField.TopologicalData

open LocalFactor.PadicAbelian

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The normalized absolute-value quasicharacter has conductor zero. -/
theorem normalizedAbsCharacter_conductorAt_zero :
    ConductorAt T T.normalizedAbsCharacter 0 := by
  apply (conductorAt_iff T _ _).mpr
  symm
  apply (T.multiplicativeConductor_eq_zero_iff _).mpr
  intro v hv
  apply Units.ext
  simp only [T.normalizedAbsCharacter_apply, Units.val_one]
  simp [normalizedAbs, ord, hv, v.ne_zero]

/-- Its value at the specified uniformizer is the spectral variable at one. -/
theorem normalizedAbsCharacter_uniformizerUnit :
    (T.normalizedAbsCharacter (uniformizerUnit T) : ℂ) = spectralVariable T 1 := by
  have hq : 0 < (T.residueCardinality : ℝ) := by
    exact_mod_cast lt_trans Nat.zero_lt_one T.residueCardinality_gt_one
  rw [T.normalizedAbsCharacter_apply, T.normalizedAbs_of_ne_zero (uniformizerUnit T).ne_zero,
    uniformizerUnit_ord]
  simp only [spectralVariable, neg_mul, one_mul, Complex.exp_neg, zpow_neg,
    zpow_one, Complex.ofReal_inv]
  rw [← Complex.ofReal_exp, Real.exp_log hq]

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure PadicAbelian

/-- The actual Tate local-analysis statement suffices for the scalar
fixed-Haar identity; its analytic premise remains explicit here. -/
def AbelianDualityFromLocalAnalysisStatement : Prop :=
  PadicAbelianLocalAnalysisStatement.{uF} → AbelianExpressionDualityStatement.{uF}

/-- Specialize the actual dual-Haar equation at zero and absorb its complementary
parameter into the normalized absolute-value twist. -/
theorem abelianDualityFromLocalAnalysis :
    AbelianDualityFromLocalAnalysisStatement.{uF} := by
  intro hA p hp F E ψ μ μ' hdual χ
  let T := fieldData F E
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace E.field := borel E.field
  let : BorelSpace E.field := ⟨rfl⟩
  let a := T.multiplicativeConductor χ
  let n := T.additiveConductor ψ
  have ha : ConductorAt T χ a := (conductorAt_iff T χ a).mpr rfl
  have hn : AdditiveConductorAt T ψ.toAddChar n :=
    (additiveConductorAt_iff T ψ n).mpr rfl
  have hnorm := T.normalizedAbsCharacter_conductorAt_zero
  have hops := (hA p E.asPadicField T).2.2.1
  have hainv : ConductorAt T χ⁻¹ a :=
    (hops χ T.normalizedAbsCharacter a 0 ha hnorm).1
  have hcomm : χ⁻¹ * T.normalizedAbsCharacter =
      T.normalizedAbsCharacter * χ⁻¹ := by
    ext x
    simp only [ContinuousMonoidHom.mul_apply, Units.val_mul]
    exact mul_comm _ _
  have hatwist : ConductorAt T (T.normalizedAbsCharacter * χ⁻¹) a := by
    rw [← hcomm]
    exact
      (hops χ⁻¹ T.normalizedAbsCharacter a 0 hainv hnorm).2.2.2 rfl
  have hatwist' : T.multiplicativeConductor
      (T.normalizedAbsCharacter * χ⁻¹) = a :=
    ((conductorAt_iff T _ a).mp hatwist).symm
  have hneg : (ψ.scale (-1)).toAddChar = ψ.toAddChar⁻¹ := by
    ext x
    simp [HarmonicAnalysis.UnitaryAdditiveCharacter.scale_apply, AddChar.inv_apply]
  have hnneg : T.additiveConductor (ψ.scale (-1)) = n := by
    rw [T.additiveConductor_scale]
    simp [PadicField.TopologicalData.ord, n]
  have hnneg' : AdditiveConductorAt T (ψ.scale (-1)).toAddChar n :=
    (additiveConductorAt_iff T _ n).mpr hnneg.symm
  rcases (hA p E.asPadicField T).2.2.2 (uniformizerUnit T)
      (uniformizerUnit_ord T) χ a ha μ with ⟨_, _, _, _, hψ⟩
  rcases hψ ψ n hn with ⟨_, _, _, _, _, _, _, _, _, hdualHaar, _, _⟩
  have hvol : (μ.measure (integerRing T)).toReal *
      (μ'.measure (integerRing T)).toReal =
      (T.residueCardinality : ℝ) ^ (-n) := by
    simpa only [PadicField.TopologicalData.integerVolume, integerRing_eq,
      MeasureTheory.measureReal_def] using fourierDualIntegerVolume F E ψ μ μ' hdual
  have heq := hdualHaar μ' hvol 0
  rcases (hA p E.asPadicField T).2.2.2 (uniformizerUnit T)
      (uniformizerUnit_ord T) χ⁻¹ a hainv μ' with ⟨_, _, _, _, hψinv⟩
  rcases hψinv (ψ.scale (-1)) n hnneg' with
    ⟨_, _, _, _, _, _, _, _, htwist, _, _, _⟩
  have hshift := ((htwist T.normalizedAbsCharacter hnorm).2 1
    T.normalizedAbsCharacter_uniformizerUnit 0).2
  have hsecond :
      epsilon T (T.normalizedAbsCharacter * χ⁻¹) (ψ.scale (-1)) μ'.measure 0 =
        epsilonAt T (uniformizerUnit T) χ⁻¹ ψ.toAddChar⁻¹ μ'.measure a n 1 := by
    simpa only [epsilon, hatwist', hnneg, hneg, zero_add, hcomm] using hshift
  rw [← deligneConstant_eq_abelianEpsilonExpression T χ ψ μ,
    ← deligneConstant_eq_abelianEpsilonExpression T
      (T.normalizedAbsCharacter * χ⁻¹) (ψ.scale (-1)) μ']
  change epsilon T χ ψ μ.measure 0 *
    epsilon T (T.normalizedAbsCharacter * χ⁻¹) (ψ.scale (-1)) μ'.measure 0 = 1
  rw [hsecond]
  simpa only [epsilon, sub_zero] using heq

/-- Actual degree-zero generation and Tate local analysis imply both unchanged
nonabelian dual functional equations. -/
theorem dualFunctionalEquation_of_generation_of_localAnalysis
    (hgen : CommonClosureDegreeZeroGenerationStatement.{uF, uV})
    (hA : PadicAbelianLocalAnalysisStatement.{uF}) :
    DualFunctionalEquationStatement.{uF, uV} :=
  dualFunctionalEquation_of_generation_of_abelianExpressionDuality hgen
    (abelianDualityFromLocalAnalysis hA)

end Langlands.LocalFactor.NonabelianSystem
