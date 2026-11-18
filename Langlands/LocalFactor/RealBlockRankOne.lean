import Langlands.LocalFactor.ArchimedeanPresentation

/-! # Real block lists of total rank one -/

namespace Langlands.Global.RankinSelbergGlobal.RealRankZero

open Langlands.LocalFactor.Archimedean

/-- A list of real blocks of total rank one is a single character block. -/
theorem eq_singleton_of_realRank_eq_one {d : List RealBlock} (h : realRank d = 1) :
    ∃ c : RealCharacterData, d = [RealBlock.character c] := by
  rcases d with _ | ⟨x, l⟩
  · exact absurd h (by rw [realRank_nil]; omega)
  · rw [realRank_cons] at h
    cases x with
    | character c =>
      rcases l with _ | ⟨y, l⟩
      · exact ⟨c, rfl⟩
      · rw [realRank_cons] at h
        cases y <;> simp only [RealBlock.rank] at h <;> omega
    | induced c =>
      simp only [RealBlock.rank] at h
      omega

end Langlands.Global.RankinSelbergGlobal.RealRankZero
