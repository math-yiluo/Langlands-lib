import Langlands.BaseChange.SplitPlace
import Langlands.BaseChange.OrbitalIntegral
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Statement: matching of test functions at a split place

For a nonarchimedean local field `F` and `F^{l+1} = Fin (l + 1) → F` with the cyclic shift
`splitCyclicShift F (l + 1)`: every Haar measure `μF` on `GL_n(F)` has a product Haar measure
`μE` on `GL_n(F^{l+1})` (`IsSplitProductHaar μF μE`), and for such measures the split tensor
`ψ₀ ⊗ ⋯ ⊗ ψ_l` and the convolution product `ψ₀ * ⋯ * ψ_l` are concordant (Arthur–Clozel 1989,
Chapter 1, §5, printed pp. 48–49, (5.1)–(5.2); Henniart–Lemaire 2011, II.2.15, printed
pp. 76–77). The statement is not proved here. See the paired Markdown.
-/

noncomputable section

open MeasureTheory

namespace Langlands.BaseChange

open HarmonicAnalysis (SchwartzBruhat)

universe u

/-- Matching at a split place (Arthur–Clozel, Chapter 1, §5; Henniart–Lemaire, II.2.15):
(a) every Haar measure `μF` on `GL_n(F)` has a Haar measure `μE` on `GL_n(F^{l+1})` with
`IsSplitProductHaar μF μE`; (b) for every such `μE`, the split tensor of
`ψ : Fin (l + 1) → SchwartzBruhat (GL_n(F))` and the convolution product of the `ψ i` are
concordant for the cyclic shift. -/
def SplitMatchingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n l : ℕ),
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    letI : MeasurableSpace (GeneralLinear n (Fin (l + 1) → F)) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    haveI : BorelSpace (GeneralLinear n (Fin (l + 1) → F)) := ⟨rfl⟩
    ∀ (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure],
      (∃ μE : Measure (GeneralLinear n (Fin (l + 1) → F)),
          μE.IsHaarMeasure ∧ IsSplitProductHaar μF μE) ∧
      ∀ (μE : Measure (GeneralLinear n (Fin (l + 1) → F))), μE.IsHaarMeasure →
        IsSplitProductHaar μF μE →
        ∀ ψ : Fin (l + 1) → SchwartzBruhat (GeneralLinear n F),
          AreConcordant (splitCyclicShift F (l + 1)) (l + 1) μF μE
            (splitTensor fun i => (ψ i : GeneralLinear n F → ℂ))
            (convolutionProduct μF ψ : GeneralLinear n F → ℂ)

end Langlands.BaseChange
