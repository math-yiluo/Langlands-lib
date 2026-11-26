import Langlands.Global.Factors.CuspidalPairEisensteinPartialOpenCell
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # Absolute convergence of the open-cell integral

For every section `φ` of the cuspidal-pair Eisenstein series, the open-cell integrand
`W_M(φ_s)(w u'(Y)) conj(ψ_N(u'(Y)))` is integrable over `M_((t+1)×(r+1))(𝔸)` on a right
half-plane of `s`. Shahidi (1981), p. 352: the local Jacquet integrals are dominated by the
corresponding intertwining integrals, which converge for `Re s` large. See the paired
Markdown. -/

set_option autoImplicit false

universe u

namespace Langlands.Global

open MeasureTheory NumberField CuspidalPairEisenstein
open Automorphic (CuspidalOperatorRealization)
open RankinSelbergGlobal (IsStandardAdditiveCharacter)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- For actual cuspidal realizations `T`, `T'` with unitary central characters, a standard
additive character `ψ` and a section `φ` (`IsSection T T' φ`), there is `σ` such that the
open-cell integrand `openCellIntegrand ψ φ s` is integrable for `openCellHaar` whenever
`σ < Re s`. -/
def CuspidalPairEisensteinOpenCellConvergenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
  ∀ φ : AdelicGL F (r + t + 2) → ℂ, IsSection T T' φ →
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
      Integrable (openCellIntegrand ψ φ s) (openCellHaar F r t)

end Langlands.Global
