import Langlands.Representation.RankinSelberg.CentralSpectralElement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-! The inverse-uniformizer scalar and its Rankin–Selberg spectral weight. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement centralSpectralElement centralSpectralElement_det_abs centralSpectralElement_mem_center determinantWeight_centralSpectralElement inverseUniformizer_normalizedAbsoluteValue normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF

variable {F : Type uF} [Field F]

/-- The scalar matrix of the inverse of the specified uniformizer. -/
def centralSpectralElement (T : LocalFieldData F) (m : ℕ) :
    Langlands.GeneralLinear m F :=
  GeneralLinear.scalar (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T)⁻¹

theorem centralSpectralElement_mem_center (T : LocalFieldData F) (m : ℕ) :
    centralSpectralElement T m ∈
      Submonoid.center (Langlands.GeneralLinear m F) := by
  exact (GeneralLinear.scalarToCenter
    (n := m) (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T)⁻¹).property

/-- The chosen inverse uniformizer has normalized absolute value equal to the
residue cardinality. -/
theorem inverseUniformizer_normalizedAbsoluteValue (T : LocalFieldData F) :
    normalizedAbsoluteValue T
      (((Langlands.LocalFactor.LocalAbelian.uniformizerUnit T)⁻¹ : Fˣ) : F) =
      (T.residueCardinality : ℝ) := by
  rw [normalizedAbsoluteValue_apply]
  simpa only [zpow_neg_one, neg_neg, zpow_one] using
    Langlands.LocalFactor.LocalAbelian.uniformizerUnit_zpow_abs T (-1)

/-- In rank `m`, the determinant absolute value of the chosen scalar is `q^m`. -/
theorem centralSpectralElement_det_abs (T : LocalFieldData F) (m : ℕ) :
    normalizedAbsoluteValue T (Matrix.det (centralSpectralElement T m).val) =
      (T.residueCardinality : ℝ) ^ m := by
  have hd : Matrix.det (centralSpectralElement T m).val =
      ((((Langlands.LocalFactor.LocalAbelian.uniformizerUnit T)⁻¹ : Fˣ) :
        F) ^ m) := by
    change ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin m)
        (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T)⁻¹)) : F) = _
    simp
  rw [hd, map_pow, inverseUniformizer_normalizedAbsoluteValue]

/-- The determinant twist evaluated at this central element is the `m`-th
power of the actual spectral parameter. -/
theorem determinantWeight_centralSpectralElement
    (T : LocalFieldData F) (m : ℕ) (s : ℂ) :
    determinantWeight (normalizedAbsoluteValue T) (centralSpectralElement T m) (-s) =
      spectralPoint T.residueCardinality s ^ m := by
  unfold determinantWeight
  rw [centralSpectralElement_det_abs, Complex.ofReal_pow, Complex.ofReal_natCast,
    ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  rfl

end Langlands.AllField.RankinSelberg
