import Langlands.HarmonicAnalysis.RowFourier
import Langlands.Group.GL.NormalizedCharacter

/-!
# P-adic row Fourier equivariance under general linear substitutions

This proposition states pullback preservation of the actual Schwartz--Bruhat
space and the plus-sign Fourier change-of-variables identity. It supplies no
proof and assumes no self-dual normalization of the supplied scalar Haar measure.
-/

namespace Langlands.HarmonicAnalysis

universe uF

/-- Right multiplication by `g` preserves the Schwartz--Bruhat test space and
transforms the row Fourier integral by the reciprocal normalized determinant
and the inverse transpose, for every supplied scalar Haar measure and every
dimension, including zero. -/
def PadicRowFourierEquivarianceStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (d : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier)
    (g : Langlands.GeneralLinear d F.Carrier)
    (Φ : SchwartzBruhat (Fin d → F.Carrier)),
    (∃ Φg : SchwartzBruhat (Fin d → F.Carrier),
      ∀ x, Φg x = Φ (Matrix.vecMul x g.val)) ∧
    (∀ Φg : SchwartzBruhat (Fin d → F.Carrier),
      (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) →
      ∀ y : Fin d → F.Carrier,
        rowFourierIntegral ψ ν d Φg y =
          ((T.normalizedAbs (Matrix.det g.val) : ℂ)⁻¹) *
            rowFourierIntegral ψ ν d Φ
              (Matrix.vecMul y (Matrix.transpose (g⁻¹).val)))

end Langlands.HarmonicAnalysis
