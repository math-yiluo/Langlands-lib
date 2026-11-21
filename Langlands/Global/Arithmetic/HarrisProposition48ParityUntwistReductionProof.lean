import Langlands.Global.Arithmetic.HarrisProposition48ParityReductionStatement

/-! # The two-place Harris parity untwist reduces to the auxiliary untwist -/

universe uF uV

namespace Langlands.Global.Harris

private theorem auxiliaryValidAtParity {Q : Proposition48Problem.{uF}} {b : ℕ}
    (h : Q.IsValidAtParity b) : Q.IsAuxiliaryValidAtParity b := by
  obtain ⟨he, hsplit, htower, hnormal, _, _, _, _, hps, hcompat, hunique, hconjUnique,
    _, _, hposition, halg, hreg, hconjInv, _, hcomponent⟩ := h
  exact ⟨he, hsplit, htower, hnormal, hps, hcompat, hunique, hconjUnique,
    hposition, halg, hreg, hconjInv, hcomponent⟩

/-- The supplied auxiliary-place untwist yields the same actual realizations
for the full two-place input. -/
theorem proposition48ParityUntwistReduction :
    Proposition48ParityUntwistReductionStatement.{uF, uV} := by
  intro hUntwist Q b ν χ χs hRaw hNorm r c hSol
  have hAuxNorm : Q.IsAuxiliaryParityNormalization b ν χs := by
    obtain ⟨hInv, hParity, hTrivial, hValid⟩ := hNorm
    have hAtRank : (Q.withCharacters (Q.correctedCharacter ν) χ χs).IsValidAtParity
        (Module.finrank Q.E Q.E' - 1) := hValid
    have hAuxAtRank := auxiliaryValidAtParity hAtRank
    exact ⟨hInv, hParity, hTrivial, hAuxAtRank⟩
  have hAuxSol :
      (Q.withCharacters (Q.correctedCharacter ν) χs χs).IsSolution.{uF, uV} c := hSol
  exact hUntwist Q b ν χs (auxiliaryValidAtParity hRaw) hAuxNorm r c hAuxSol

end Langlands.Global.Harris
