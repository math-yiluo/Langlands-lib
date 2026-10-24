import Langlands.Representation.RankinSelberg.IntegrandContinuityStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker QuotientIntegration

universe uF uV uW

/-- The actual equal-rank quotient integrand is continuous for smooth
coefficient models, including zero functionals and reducible representations. -/
theorem equalRankIntegrandContinuous (F : Type uF) [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] (n : ℕ) :
    EqualRankIntegrandContinuousStatement.{uF, uV, uW} F n := by
  intro abv habv V _ _ W _ _ π σ hπ hσ ψ ℓ ℓ' f f' Φ s
  have hf : Continuous f.val.val := by
    obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
    exact (Langlands.matrixCoefficient_isLocallyConstant π ℓ.val v (hπ v)).continuous
  have hf' : Continuous f'.val.val := by
    obtain ⟨v, rfl⟩ := modelMap_surjective σ ℓ' f'
    exact (Langlands.matrixCoefficient_isLocallyConstant σ ℓ'.val v (hσ v)).continuous
  have hrow : Continuous (lastRow : Langlands.GeneralLinear (n + 1) F → _) := by
    apply continuous_pi
    intro j
    exact (Units.continuous_val.matrix_elem (Fin.last n) j)
  have hdet : Continuous (fun g : Langlands.GeneralLinear (n + 1) F =>
      abv (Matrix.det g.val)) := habv.comp Units.continuous_val.matrix_det
  have hweight : Continuous (fun g : Langlands.GeneralLinear (n + 1) F =>
      determinantWeight abv g s) := by
    apply (Complex.continuous_ofReal.comp hdet).cpow continuous_const
    intro g
    exact Complex.ofReal_mem_slitPlane.mpr (abv.pos g.det_ne_zero)
  apply (leftQuotient_isOpenQuotientMap
    (GeneralLinear.upperUnipotent (n + 1) F)).isQuotientMap.continuous_iff.mpr
  exact ((hf.mul hf').mul (Φ.locallyConstant.continuous.comp hrow)).mul hweight

end Langlands.RankinSelberg
