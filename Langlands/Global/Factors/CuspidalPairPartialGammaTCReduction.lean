import Langlands.Global.Factors.CuspidalPairPartialGammaEquationTCStatement
import Langlands.Global.Factors.CuspidalSatakeBoundReduction
import Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement
import Langlands.Automorphic.IrreducibleCentralCharacterProof

/-!
# The totally complex completed equation of cuspidal pairs from the totally complex partial equation

`CuspidalPairPartialGammaEquationTCStatement` is the published
`CuspidalPairPartialGammaEquationStatement` (the partial functional equation with integral
gamma factors) with the instance argument `[NumberField.IsTotallyComplex F]` inserted after
`[NumberField F]`, at the same universe levels, the rest verbatim.

`cuspidalPairPartialGammaTCReduction` proves that it implies
`CuspidalPairCompletedEquationTCStatement`. The proof applies, one number field at a time,
the two published per-field steps `FinitePairFactorChoice.continuationHolds_of_partialGamma`
and `FinitePairFactorChoice.completedEquationHolds_of_continuationHolds`, with the Satake
bounds supplied by the proved `CuspidalSatakeBoundStatement`. See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField HeckeFunctionalEquation CuspidalPairFunctionalEquation
open CuspidalPairBoundaryNonvanishing
open LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)

/-- The totally complex partial equation with integral gamma factors implies the totally
complex completed equation of cuspidal pairs for every admissible exceptional set. -/
def CuspidalPairPartialGammaTCReductionStatement : Prop :=
  CuspidalPairPartialGammaEquationTCStatement.{u, uQ} →
    CuspidalPairCompletedEquationTCStatement.{u, uQ}

/-- The unrestricted partial equation implies its totally complex form (forget the
instance). -/
theorem cuspidalPairPartialGammaEquationTC_of_partialGamma
    (hG : CuspidalPairPartialGammaEquationStatement.{u, uQ}) :
    CuspidalPairPartialGammaEquationTCStatement.{u, uQ} :=
  fun F _ _ _ _ => hG F

/-- The reduction: the totally complex partial equation with integral gamma factors
implies the totally complex completed equation. The Satake bounds come from the proved
`CuspidalSatakeBoundStatement`. -/
theorem cuspidalPairPartialGammaTCReduction :
    CuspidalPairPartialGammaTCReductionStatement.{u, uQ} := by
  intro hG F _ _ _ _ ψ hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' hd hd' S hP
    hP' hPd hPd' hsupp c hc aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd'
    hdC hdC' hdCd hdCd'
  have hSat : CuspidalSatakeBoundStatement.{u, uQ} :=
    cuspidalSatakeBoundReduction Automorphic.OperatorRealization.irreducibleCentralCharacter
  obtain ⟨A, hA⟩ := hSat F r T P h
  obtain ⟨B, hB⟩ := hSat F t T' P' h'
  obtain ⟨Ad, hAd⟩ := hSat F r Td Pd hd
  obtain ⟨Bd, hBd⟩ := hSat F t Td' Pd' hd'
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hprod, hprodd, hfe⟩ := hG F ψ hψ hdiag r t T Td T' Td' hTd hTd'
    P P' Pd Pd' h h' hd hd' S hP hP' hPd hPd' hsupp aR haR aC haC dR dR' dRd dRd' hdR hdR'
    hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
  exact c.completedEquationHolds_of_continuationHolds hP hP' hPd hPd' hc hA hB hAd hBd
    (c.continuationHolds_of_partialGamma hP hP' hPd hPd' hc hΛ hΛd hprod hprodd
      (fun v s => RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s)
        (RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection (padicField v))
          (c.epsilon v).1 (c.epsilon v).2 (c.lPolynomial v) (c.dualLPolynomial v)))
      (hfe c.additive c.additive_spec c.measure c.measure_spec _
        (fun v _ => c.isPadicSymmetricGammaFactor hTd hTd' v))
      (fun v _ => c.eventually_finiteL_mul_gamma v))

/-- The unrestricted completed equation implies its totally complex form (forget the
instance). -/
theorem cuspidalPairCompletedEquationTC_of_completedEquation
    (h : CuspidalPairCompletedEquationStatement.{u, uQ}) :
    CuspidalPairCompletedEquationTCStatement.{u, uQ} :=
  fun F _ _ _ _ => h F

end Langlands.Global
