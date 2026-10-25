import Langlands.LocalField.Uniformizer
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-! The inverse-uniformizer scalar and its Rankin–Selberg spectral weight. -/

noncomputable section

namespace Langlands.RankinSelberg

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The scalar matrix of the inverse of the specified uniformizer. -/
def centralSpectralElement (T : F.TopologicalData) (m : ℕ) :
    Langlands.GeneralLinear m F.Carrier :=
  GeneralLinear.scalar (LocalFactor.PadicAbelian.uniformizerUnit T)⁻¹

theorem centralSpectralElement_mem_center (T : F.TopologicalData) (m : ℕ) :
    centralSpectralElement T m ∈
      Submonoid.center (Langlands.GeneralLinear m F.Carrier) := by
  exact (GeneralLinear.scalarToCenter
    (n := m) (LocalFactor.PadicAbelian.uniformizerUnit T)⁻¹).property

/-- The chosen inverse uniformizer has normalized absolute value equal to the
residue cardinality. -/
theorem inverseUniformizer_normalizedAbsoluteValue (T : F.TopologicalData) :
    normalizedAbsoluteValue T
      (((LocalFactor.PadicAbelian.uniformizerUnit T)⁻¹ : F.Carrierˣ) : F.Carrier) =
      (T.residueCardinality : ℝ) := by
  rw [normalizedAbsoluteValue_apply]
  simpa only [zpow_neg_one, neg_neg, zpow_one] using
    LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T (-1)

/-- In rank `m`, the determinant absolute value of the chosen scalar is `q^m`. -/
theorem centralSpectralElement_det_abs (T : F.TopologicalData) (m : ℕ) :
    normalizedAbsoluteValue T (Matrix.det (centralSpectralElement T m).val) =
      (T.residueCardinality : ℝ) ^ m := by
  have hd : Matrix.det (centralSpectralElement T m).val =
      ((((LocalFactor.PadicAbelian.uniformizerUnit T)⁻¹ : F.Carrierˣ) :
        F.Carrier) ^ m) := by
    change ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin m)
        (LocalFactor.PadicAbelian.uniformizerUnit T)⁻¹)) : F.Carrier) = _
    simp
  rw [hd, map_pow, inverseUniformizer_normalizedAbsoluteValue]

/-- The determinant twist evaluated at this central element is the `m`-th
power of the actual spectral parameter. -/
theorem determinantWeight_centralSpectralElement
    (T : F.TopologicalData) (m : ℕ) (s : ℂ) :
    determinantWeight (normalizedAbsoluteValue T) (centralSpectralElement T m) (-s) =
      spectralPoint T.residueCardinality s ^ m := by
  unfold determinantWeight
  rw [centralSpectralElement_det_abs, Complex.ofReal_pow, Complex.ofReal_natCast,
    ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  rfl

end Langlands.RankinSelberg
