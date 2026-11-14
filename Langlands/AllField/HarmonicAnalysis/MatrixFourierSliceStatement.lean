import Langlands.HarmonicAnalysis.MatrixFourierSliceStatement
import Langlands.AllField.Group.GL.PadicSupplement
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierSurjectivityStatement
/-!
# Rectangular Fourier slices of last-row cutoffs

Statement of the scalar Fourier step in the proof of JPSS Proposition 9.1,
printed 452–454: every Schwartz–Bruhat cutoff of the last row of `g` is the
twisted rectangular integral of `x ↦ Ψ(g⁻¹ x)` for one Schwartz–Bruhat `Ψ`.
The statement is conditional on row Fourier surjectivity in the row dimension.
This is a proposition definition, not a proof.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement
open Langlands.AllField.HarmonicAnalysis

universe u

/-- Conditional on Fourier surjectivity for rows of length `b + 1`, every
Schwartz–Bruhat cutoff `Φ` admits a Schwartz–Bruhat function `Ψ` on
`(b + 1) × (a + 1)` matrices with
`∫ ψ(-x_{b,0}) Ψ(g⁻¹ x) dx = |det g|^(a + 1) Φ(lastRow g)` for every
`g ∈ GL_{b+1}`. The integral uses the product of the supplied scalar Haar
measure over all entries; `T` supplies the topology and the normalized
absolute value, and the scalar measurable space is Borel. -/
def PadicMatrixFourierSliceStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (a b : ℕ),
    PadicRowFourierSurjectivityStatement F T (b + 1) →
    letI := T.topology
    letI := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
      (Φ : SchwartzBruhat (Fin (b + 1) → F)),
      ∃ Ψ : SchwartzBruhat (Matrix (Fin (b + 1)) (Fin (a + 1)) F),
        ∀ g : GeneralLinear (b + 1) F,
          ∫ x, ψ.complex (-(x (Fin.last b) 0)) *
              Ψ ((g⁻¹ : GeneralLinear (b + 1) F).val * x)
            ∂RankinSelberg.rectangularMeasure ν (b + 1) (a + 1) =
            (T.normalizedAbs (Matrix.det g.val) : ℂ) ^ (a + 1) *
              Φ (RankinSelberg.lastRow g)

end Langlands.AllField.HarmonicAnalysis
