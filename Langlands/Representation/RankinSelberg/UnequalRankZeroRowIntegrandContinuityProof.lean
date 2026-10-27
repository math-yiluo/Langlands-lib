import Langlands.Representation.RankinSelberg.UnequalRankZeroRowIntegrandContinuityStatement
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Group.GL.NormalizedCharacter
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

section
variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- Worker 331's helper: `diag(g, I_d)` is continuous. -/
private theorem appendIdentity_continuous (n d : ℕ) :
    Continuous (appendIdentity (F := F) n d) := by
  have hv : Continuous (fun g : Langlands.GeneralLinear (n + 1) F =>
      (appendIdentity n d g).val) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [appendIdentity_entry]
    split_ifs
    · exact Units.continuous_val.matrix_elem _ _
    all_goals exact continuous_const
  apply Units.continuous_iff.mpr
  refine ⟨hv, ?_⟩
  simpa only [Function.comp_def, map_inv] using hv.comp continuous_inv
end

theorem unequalRankZeroRowIntegrandContinuous (F : Type uF) [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] (n k : ℕ) :
    UnequalRankZeroRowIntegrandContinuousStatement.{uF, uV, uW} F n k := by
  intro abv habv V _ _ W _ _ π σ hπ hσ ψ ℓ ℓ' f f' s
  have hf : Continuous f.val.val := by
    obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
    exact (Langlands.matrixCoefficient_isLocallyConstant π ℓ.val v (hπ v)).continuous
  have hf' : Continuous f'.val.val := by
    obtain ⟨v, rfl⟩ := modelMap_surjective σ ℓ' f'
    exact (Langlands.matrixCoefficient_isLocallyConstant σ ℓ'.val v (hσ v)).continuous
  have hdet : Continuous (fun g : Langlands.GeneralLinear (n + 1) F =>
      abv (Matrix.det g.val)) := habv.comp Units.continuous_val.matrix_det
  have hweight : Continuous (fun g : Langlands.GeneralLinear (n + 1) F =>
      determinantWeight abv g (s - ((0 + k + 1 : ℕ) : ℂ) / 2)) := by
    apply (Complex.continuous_ofReal.comp hdet).cpow continuous_const
    intro g
    exact Complex.ofReal_mem_slitPlane.mpr (abv.pos g.det_ne_zero)
  apply (leftQuotient_isOpenQuotientMap
    (upperUnipotent (n + 1) F)).isQuotientMap.continuous_iff.mpr
  change Continuous (fun g => f.val.val (unequalRankMatrix 0 k g 0) * f'.val.val g *
    determinantWeight abv g (s - ((0 + k + 1 : ℕ) : ℂ) / 2))
  simp only [unequalRankMatrix_zero_rows]
  exact (hf.comp (appendIdentity_continuous (F := F) n (0 + k + 1))).mul hf' |>.mul hweight

/-- Arbitrary-`T` p-adic specialization check. -/
example {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    UnequalRankZeroRowIntegrandContinuousStatement.{uF, uV, uW} F.Carrier n k →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      IsSmooth π → IsSmooth σ →
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
        (ℓ : glFunctionals ψ (n + (0 + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ)
        (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule) (s : ℂ),
        Continuous (unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k
          f.val f'.val s 0) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro h
  exact h (normalizedAbsoluteValue T)
    (NNReal.continuous_coe.comp T.continuous_normalizedAbsHom)

end Langlands.RankinSelberg
