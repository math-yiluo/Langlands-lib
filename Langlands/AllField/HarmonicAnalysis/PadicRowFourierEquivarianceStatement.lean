import Langlands.HarmonicAnalysis.PadicRowFourierEquivarianceStatement
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
/-!
# P-adic row Fourier equivariance under general linear substitutions

This proposition states pullback preservation of the actual Schwartz--Bruhat
space and the plus-sign Fourier change-of-variables identity. It supplies no
proof and assumes no self-dual normalization of the supplied scalar Haar measure.
-/

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement
open Langlands.AllField.HarmonicAnalysis

universe uF

/-- Right multiplication by `g` preserves the Schwartz--Bruhat test space and
transforms the row Fourier integral by the reciprocal normalized determinant
and the inverse transpose, for every supplied scalar Haar measure and every
dimension, including zero. -/
def PadicRowFourierEquivarianceStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (d : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI : MeasurableSpace F := borel F
  letI : BorelSpace F := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F)
    (ν : AdditiveHaarMeasure F)
    (g : Langlands.GeneralLinear d F)
    (Φ : SchwartzBruhat (Fin d → F)),
    (∃ Φg : SchwartzBruhat (Fin d → F),
      ∀ x, Φg x = Φ (Matrix.vecMul x g.val)) ∧
    (∀ Φg : SchwartzBruhat (Fin d → F),
      (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) →
      ∀ y : Fin d → F,
        rowFourierIntegral ψ ν d Φg y =
          ((T.normalizedAbs (Matrix.det g.val) : ℂ)⁻¹) *
            rowFourierIntegral ψ ν d Φ
              (Matrix.vecMul y (Matrix.transpose (g⁻¹).val)))

end Langlands.AllField.HarmonicAnalysis
