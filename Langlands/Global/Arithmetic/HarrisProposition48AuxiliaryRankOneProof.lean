import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryInputStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerAuxiliaryRankOneProof

/-! # The auxiliary rank-one case of Harris's Proposition 4.8 -/

universe uF uV

namespace Langlands.Global.Harris

/-- The character line with its complex-place parameters supplies the four
solution properties required for the one-place rank-one start. -/
theorem proposition48AuxiliaryRankOne : Proposition48AuxiliaryRankOneStatement.{uF, uV} := by
  intro Q hQ h1
  obtain ⟨r, c, hc, _⟩ := proposition48ExactStabilizerAuxiliaryRankOne.{uF, uV} Q hQ h1
  exact ⟨r, c, hc⟩

end Langlands.Global.Harris
