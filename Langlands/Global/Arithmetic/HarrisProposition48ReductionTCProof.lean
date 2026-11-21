import Langlands.Global.Arithmetic.HarrisProposition48ReductionProof
import Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement

/-!
# Proof of the totally complex reduction of Harris's Proposition 4.8

The same one-place induction as `proposition48Reduction`, with the branch
hypothesis supplied by the totally complex prime and singleton branches and
their totally complex foundational inputs.
-/

noncomputable section

universe uF uV

namespace Langlands.Global.Harris

/-- The exact target `Proposition48ReductionTCStatement`: the fourteen
explicit inputs, with inputs 5, 6 and 9–14 in their totally complex forms,
imply the unchanged `Proposition48Statement.{uF, 0, 0, 0, uV}`. -/
theorem proposition48ReductionTC : Proposition48ReductionTCStatement.{uF, uV} := by
  intro h
  obtain ⟨hRank, hNorm, hUntwist, hMackey, hPrime, hSingleton, hThm12, hComp, hRigid, hInv,
    hInd, hLift, hDesc, hWeak⟩ := h
  refine proposition48_of_hasSolution fun Q hQ ↦
    Proposition48Problem.hasSolution_of_isAuxiliaryValid hRank hNorm hUntwist hMackey ?_ Q hQ
  intro Q D hQ hD hcard hchildren
  rcases hcard with h1 | hp
  · exact hSingleton hThm12 hRigid hInv hDesc Q D hQ hD h1 hchildren
  · exact hPrime hThm12 hComp hRigid hInv hInd hLift hWeak Q D hQ hD hp hchildren

end Langlands.Global.Harris
