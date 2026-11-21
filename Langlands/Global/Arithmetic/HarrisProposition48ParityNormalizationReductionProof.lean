import Langlands.Global.Arithmetic.HarrisProposition48ParityReductionStatement

/-! # Reduction of two-place Harris parity normalization to auxiliary normalization -/

universe uF

namespace Langlands.Global.Harris

/-- Auxiliary parity normalization extends to both places by transporting the
primary component with the same correcting character. -/
theorem proposition48ParityNormalizationReduction :
    Proposition48ParityNormalizationReductionStatement.{uF} := by
  intro normalizeAuxiliary transportPlace Q b hRaw
  obtain ⟨hRec, hSplit, hTower, hNormal, hAbove, hCompatible, hUnique, hUniqueConj,
    hAboveAux, hCompatibleAux, hUniqueAux, hUniqueConjAux, hDistinct, hDistinctConj,
    hGeneralPosition, hAlgebraic, hRegular, hConjugateInverse, hComponent, hComponentAux⟩ := hRaw
  have hRawAux : Q.IsAuxiliaryValidAtParity b :=
    ⟨hRec, hSplit, hTower, hNormal, hAboveAux, hCompatibleAux, hUniqueAux, hUniqueConjAux,
      hGeneralPosition, hAlgebraic, hRegular, hConjugateInverse, hComponentAux⟩
  obtain ⟨ν, χs, hConjν, hAlgν, hTrivialν, hCorrectedAux⟩ := normalizeAuxiliary Q b hRawAux
  obtain ⟨χ, _, hCorrectedComponent, _⟩ :=
    transportPlace Q Q.P ν Q.χ hRec hAbove hCompatible hComponent
  obtain ⟨_, _, _, _, _, _, _, _, hCorrectedGeneralPosition, hCorrectedAlgebraic,
    hCorrectedRegular, hCorrectedConjugateInverse, hCorrectedComponentAux⟩ := hCorrectedAux
  exact ⟨ν, χ, χs, hConjν, hAlgν, hTrivialν, hRec, hSplit, hTower, hNormal, hAbove,
    hCompatible, hUnique, hUniqueConj, hAboveAux, hCompatibleAux, hUniqueAux, hUniqueConjAux,
    hDistinct, hDistinctConj, hCorrectedGeneralPosition, hCorrectedAlgebraic, hCorrectedRegular,
    hCorrectedConjugateInverse, hCorrectedComponent, hCorrectedComponentAux⟩

end Langlands.Global.Harris
