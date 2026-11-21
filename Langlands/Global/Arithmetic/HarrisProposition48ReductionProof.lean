import Langlands.Global.Arithmetic.HarrisProposition48ReductionStatement

/-!
# Proof of the explicit-input reduction of Harris's Proposition 4.8

The one-place induction on the normal-closure degree `[L : E]` of a
`Proposition48Problem`, with the rank-one, parity, Mackey-step and branch
inputs taken as hypotheses, followed by the recovery of the unchanged
`Proposition48Statement` from an original datum. The branch is abstracted so
that the same induction also serves the totally complex companion.
-/

noncomputable section

universe uF uV

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.GaloisRepresentation
open LocalFactor.CommonClosure

namespace Proposition48Problem

/-- Changing the three characters changes no field, so the induction degree
`[L : E]` is unchanged. -/
theorem inductionDegree_withCharacters (Q : Proposition48Problem.{uF})
    (ξ : HeckeCharacter Q.E') (χ χs : FieldCharacter Q.F Q.F') :
    (Q.withCharacters ξ χ χs).inductionDegree = Q.inductionDegree :=
  rfl

/-- `HasSolution` is the existence of a cuspidal class with the four
properties of `IsSolution`. -/
theorem hasSolution_iff (Q : Proposition48Problem.{uF}) :
    Q.HasSolution.{uF, uV} ↔
      ∃ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r), Q.IsSolution.{uF, uV} c :=
  Iff.rfl

/-- One child of the Mackey step, at the inherited parity and of smaller
degree, yields the normalized and untwisted child data required by both
branches: normalize the parity, solve the corrected child by the induction
hypothesis on the same fields, and untwist on actual realizations. -/
theorem exists_untwistedSolution_of_child
    (hNorm : Proposition48AuxiliaryParityNormalizationStatement.{uF})
    (hUntwist : Proposition48AuxiliaryParityUntwistStatement.{uF, uV})
    (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L) (a : Q.L ≃ₐ[Q.E] Q.L)
    (ih : ∀ R : Proposition48Problem.{uF}, R.inductionDegree < Q.inductionDegree →
      R.IsAuxiliaryValid → R.HasSolution.{uF, uV})
    (R : Proposition48Problem.{uF}) (hchild : Q.IsAuxiliaryMackeyChild D a R)
    (hvalid : R.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1))
    (hrank : Module.finrank R.E R.E' = Q.mackeyRank D a)
    (hdeg : R.inductionDegree < Q.inductionDegree) :
    ∃ (ν : HeckeCharacter R.E) (χs : FieldCharacter R.F R.F') (r : ℕ)
      (S T : CuspidalOperatorRealization R.E r),
      Q.IsAuxiliaryMackeyChild D a R ∧
      R.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
      Module.finrank R.E R.E' = Q.mackeyRank D a ∧
      R.inductionDegree < Q.inductionDegree ∧
      R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
      R.IsUntwistedSolution.{uF, uV} ν S T := by
  obtain ⟨ν, χs, hν⟩ := hNorm R _ hvalid
  have hcorr : (R.withCharacters (R.correctedCharacter ν) χs χs).IsAuxiliaryValid := hν.2.2.2
  have hdeg' : (R.withCharacters (R.correctedCharacter ν) χs χs).inductionDegree <
      Q.inductionDegree := by
    rwa [inductionDegree_withCharacters]
  obtain ⟨r, c, hc⟩ := (hasSolution_iff _).1 (ih _ hdeg' hcorr)
  obtain ⟨S, T, -, hST⟩ := hUntwist R _ ν χs hvalid hν r c hc
  exact ⟨ν, χs, r, S, T, hchild, hvalid, hrank, hdeg, hν, hST⟩

/-- The one-place induction on the normal-closure degree `[L : E]`. The
branch hypothesis `hBranch` stands for the prime and singleton branches
(with their foundational inputs already applied); rank one uses the
auxiliary rank-one input. -/
theorem hasSolution_of_isAuxiliaryValid
    (hRank : Proposition48AuxiliaryRankOneStatement.{uF, uV})
    (hNorm : Proposition48AuxiliaryParityNormalizationStatement.{uF})
    (hUntwist : Proposition48AuxiliaryParityUntwistStatement.{uF, uV})
    (hMackey : Proposition48MackeyStepStatement.{uF})
    (hBranch : ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryValid → Q.IsPrimeCyclicStep D →
      (Nat.card (Q.MackeyIndex D) = 1 ∨
        Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D) →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T) →
      Q.HasSolution.{uF, uV})
    (Q : Proposition48Problem.{uF}) (hQ : Q.IsAuxiliaryValid) : Q.HasSolution.{uF, uV} := by
  suffices h : ∀ (n : ℕ) (Q : Proposition48Problem.{uF}), Q.inductionDegree = n →
      Q.IsAuxiliaryValid → Q.HasSolution.{uF, uV} from
    h _ Q rfl hQ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hn hQ
    subst hn
    have ih' : ∀ R : Proposition48Problem.{uF}, R.inductionDegree < Q.inductionDegree →
        R.IsAuxiliaryValid → R.HasSolution.{uF, uV} :=
      fun R hR hRv ↦ ih _ hR R rfl hRv
    have hpos : 0 < Module.finrank Q.E Q.E' := Module.finrank_pos
    rcases Nat.lt_or_ge 1 (Module.finrank Q.E Q.E') with hgt | hle
    · obtain ⟨D, hD, hcard, hchildren⟩ := hMackey Q hQ hgt
      refine hBranch Q D hQ hD hcard fun a ↦ ?_
      obtain ⟨R, hchild, hvalid, hrank, hdeg⟩ := hchildren a
      obtain ⟨ν, χs, r, S, T, hR⟩ :=
        exists_untwistedSolution_of_child hNorm hUntwist Q D a ih' R hchild hvalid hrank hdeg
      exact ⟨R, ν, χs, r, S, T, hR⟩
    · exact hRank Q hQ (by omega)

end Proposition48Problem

/-- An original datum of `Proposition48Statement` over small fields is a
`Proposition48Problem` whose full validity implies auxiliary validity, and
whose `HasSolution` is exactly the original four-part conclusion. -/
theorem proposition48_of_hasSolution
    (h : ∀ Q : Proposition48Problem.{uF}, Q.IsAuxiliaryValid → Q.HasSolution.{uF, uV}) :
    Proposition48Statement.{uF, 0, 0, 0, uV} := by
  intro p _ F F' E E' L _ _ _ _ _ _ _ _ _ _ _ _ e χ χs K₀ P Ps ξ hnr hdatum
  obtain ⟨hK, hST, hNC, -, -, -, -, hpPs, hPsc, hUPs, hUcPs, -, -, hgp, halg, hreg, hci, -,
    hPscomp⟩ := hdatum
  exact h
    { p := p, F := F, F' := F', E := E, E' := E', L := L
      e := e, χ := χ, χs := χs, K₀ := K₀, P := P, Ps := Ps, ξ := ξ }
    ⟨hnr, hK, hST, hNC, hpPs, hPsc, hUPs, hUcPs, hgp, halg, hreg, hci, hPscomp⟩

/-- The exact target `Proposition48ReductionStatement`: the fourteen explicit
inputs imply the unchanged `Proposition48Statement.{uF, 0, 0, 0, uV}`. -/
theorem proposition48Reduction : Proposition48ReductionStatement.{uF, uV} := by
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
