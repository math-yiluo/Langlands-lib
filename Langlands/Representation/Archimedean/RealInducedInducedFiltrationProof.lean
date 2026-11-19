import Langlands.Representation.Archimedean.RealInducedPairFiltrationReduction
import Langlands.Representation.Archimedean.RealInducedPairLeftZero
import Langlands.Representation.Archimedean.RealInducedPairRightZero
import Langlands.Representation.Archimedean.RealInducedPairUnlinkedFiltration
import Langlands.Representation.Archimedean.RealInducedPairNegativeBraidFiltrationClosure
import Langlands.Representation.Archimedean.RealInducedPairZeroInnerFiltration
import Langlands.Representation.Archimedean.RealInducedPairPositiveFiltration

/-! # The adjacent filtration for two induction blocks on GL₄(ℝ) -/

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealInducedPairLinkedReplacement

/-- The adjacent filtration for two induction blocks in strictly ascending exponent order. -/
theorem realInducedInducedFiltration : RealInducedInducedFiltrationStatement := by
  intro d e hlt
  by_cases hd : d.weight = 0
  · exact RealInducedPairLeftZero.filtration 4 [] [] d e hd rfl hlt
  by_cases he : e.weight = 0
  · exact RealInducedPairRightZero.filtration 4 [] [] d e he rfl hlt
  by_cases hlinked : ∃ k : ℕ, IsLinkedAt d e k
  · obtain ⟨k, hk⟩ := hlinked
    have hdp : 0 < d.weight.natAbs := Int.natAbs_pos.mpr hd
    have hep : 0 < e.weight.natAbs := Int.natAbs_pos.mpr he
    rcases lt_trichotomy (innerWeight d e k) 0 with hn | hz | hp
    · exact realInducedPairFiltration_of_negativeInner hk hn
    · exact RealInducedPairZeroInnerFiltration.filtration hdp hep hk hz
    · exact RealInducedPairPositiveFiltration.filtration hdp hep hk hp
  · exact RealInducedPairUnlinkedFiltration.filtration d e hlt (fun k hk => hlinked ⟨k, hk⟩)

end Langlands.Archimedean
