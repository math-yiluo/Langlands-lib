import Langlands.HarmonicAnalysis.Distribution.CharacterAverage

/-!
# Translation covariance of character-weighted product averaging

A statement only. Translating a test function on `G × (Y × G)` on the left in the
first factor by `a` and on the right in the last factor by `b` multiplies its
character average by `χ a * χ b`, provided the measure on `G` is both left and right
invariant. See the paired Markdown for the sign, the hypotheses and the provenance.
-/

namespace Langlands.HarmonicAnalysis.SchwartzBruhat

open MeasureTheory

universe uG uY

/-- For a topological group `G` with its Borel structure, a topological space `Y`, a
continuous character `χ : G →* ℂˣ`, an s-finite measure `μ` on `G` that is finite on
compact sets and both left and right invariant, elements `a b : G`, and a test function
`α` on `G × (Y × G)`: pulling `α` back along `(g₁, (y, g₂)) ↦ (a * g₁, (y, g₂ * b))`
multiplies `characterAverage χ μ α` by `(χ a : ℂ) * (χ b : ℂ)`. -/
def CharacterAverageCovarianceStatement : Prop :=
  ∀ (G : Type uG) (Y : Type uY) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [TopologicalSpace Y]
    (χ : ContinuousMonoidHom G ℂˣ) (μ : Measure G) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (a b : G) (α : SchwartzBruhat (G × (Y × G))),
      characterAverage χ μ
          (Hecke.TestFunction.pullback
            ((Homeomorph.mulLeft a).prodCongr
              ((Homeomorph.refl Y).prodCongr (Homeomorph.mulRight b))) α) =
        ((χ a : ℂ) * (χ b : ℂ)) • characterAverage χ μ α

end Langlands.HarmonicAnalysis.SchwartzBruhat
