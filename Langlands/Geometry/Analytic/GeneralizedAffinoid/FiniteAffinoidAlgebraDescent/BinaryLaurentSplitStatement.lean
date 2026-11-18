import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.LocalData
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SplitSquareIdealDescent

/-! # Real-radius binary Laurent splits of full domains are split squares -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open FiniteAffinoidAlgebraDescent

/-- For every full domain `U`, every `a` in its algebra and every real radius
`ρ > 0`, full domains with the loci `{|a| ≤ ρ}` and `{|a| ≥ ρ}` inside `U` exist,
and for any such domains and any full domain on their intersection locus, the
four original restrictions form a `BoundedAlgHom.SplitSquare`. -/
def DomainBinaryLaurentSplitSquareStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (R : PresentedAffinoidAlgebra K) (U : Domain K R) (a : U.algebra) (ρ : ℝ),
    0 < ρ →
      (∃ U₁ U₂ : Domain K R,
        U₁.locus = U.spectrumMap '' {y | y a ≤ ρ} ∧
          U₂.locus = U.spectrumMap '' {y | ρ ≤ y a}) ∧
      ∀ (U₁ U₂ W : Domain K R) (h₁ : U₁.locus ⊆ U.locus) (h₂ : U₂.locus ⊆ U.locus)
        (hW₁ : W.locus ⊆ U₁.locus) (hW₂ : W.locus ⊆ U₂.locus),
        U₁.locus = U.spectrumMap '' {y | y a ≤ ρ} →
        U₂.locus = U.spectrumMap '' {y | ρ ≤ y a} →
        W.locus = U₁.locus ∩ U₂.locus →
        Nonempty (BoundedAlgHom.SplitSquare (restriction h₁) (restriction h₂)
          (restriction hW₁) (restriction hW₂))

end Langlands.Analytic.PresentedAffinoidAlgebra
