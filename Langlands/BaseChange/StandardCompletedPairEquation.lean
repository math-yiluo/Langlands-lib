import Langlands.BaseChange.FinitePairFactorNonvanishing
import Langlands.BaseChange.StandardArchimedeanComparison
import Langlands.Global.Factors.CuspidalPairFunctionalEquationStatement
import Langlands.Global.Factors.CuspidalPairPoleAdditiveInputs

/-! # The completed pair equation in standard additive normalization -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.BaseChange

open NumberField Automorphic Global Global.HeckeFunctionalEquation
open Automorphic.CuspidalWhittaker LocalFactor.Archimedean
open Global.CuspidalPairFunctionalEquation Global.FunctionalEquationComparison.RelativeWeilEngine
open scoped BigOperators

/-- The global pair functional equation yields an equation at the standard adelic character
with Gamma products of the stated counts and a constant archimedean epsilon factor.
The finite factor choices are the actual choices for the supplied presentations. -/
def StandardCompletedPairEquationStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{u, uQ} →
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r t : ℕ) (T Td : CuspidalOperatorRealization K r) (T' Td' : CuspidalOperatorRealization K t),
    Td.realization.IsContragredientOf T.realization → Td'.realization.IsContragredientOf T'.realization →
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T')
      (Pd : CuspidalSpectralPresentation.{u, uQ} Td) (Pd' : CuspidalSpectralPresentation.{u, uQ} Td')
      (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
      (hd : HasIrreducibleAdmissibleComponents Pd) (hd' : HasIrreducibleAdmissibleComponents Pd'),
      ∃ (c : FinitePairFactorChoice (standardGlobalAdditiveCharacter K) P P' Pd Pd' h h' hd hd')
        (S : Finset (Global.FinitePlace K)) (A Ad : List GammaBlock) (ε : ℂˣ),
        ((A.flatMap GammaBlock.realShifts).length = Module.finrank ℚ K * ((r + 1) * (t + 1))) ∧
        ((Ad.flatMap GammaBlock.realShifts).length = Module.finrank ℚ K * ((r + 1) * (t + 1))) ∧
        (∀ v ∉ S, c.epsilon v = (1, 0)) ∧
        HasGlobalEquation c.finiteL c.finiteDualL c.finiteEpsilon
          (fun z => ((gammaProduct A).denominator z)⁻¹)
          (fun z => ((gammaProduct Ad).denominator z)⁻¹) (fun _ => (ε : ℂ)) S

set_option maxHeartbeats 1400000 in
/-- Specialize the completed equation to the standard character and use the actual
archimedean parameters to supply its Gamma blocks and constant. -/
theorem standardCompletedPairEquation : StandardCompletedPairEquationStatement.{u, uQ} := by
  classical
  intro hFE K _ _ _ r t T Td T' Td' hD hD' P P' Pd Pd' h h' hd hd'
  have hψ : ∃ x : Adeles K, standardGlobalAdditiveCharacter K x ≠ 1 := exists_adelicCharacter_ne_one K
  obtain ⟨⟨⟨c⟩, hR, hC⟩, S, hS, hS', hSd, hSd', -, hEq⟩ := hFE K
    (standardGlobalAdditiveCharacter K) hψ (standardGlobalAdditiveCharacter_diagonal K)
    r t T Td T' Td' hD hD' P P' Pd Pd' h h' hd hd'
  choose dR hdR using fun v => (hR v).2.1
  choose dR' hdR' using fun v => (hR v).2.2.1
  choose dRd hdRd using fun v => (hR v).2.2.2.1
  choose dRd' hdRd' using fun v => (hR v).2.2.2.2
  choose dC hdC using fun v => (hC v).2.1
  choose dC' hdC' using fun v => (hC v).2.2.1
  choose dCd hdCd using fun v => (hC v).2.2.2.1
  choose dCd' hdCd' using fun v => (hC v).2.2.2.2
  obtain ⟨hUnram, hEq⟩ := hEq c
  have hStdR (v : {v : NumberField.InfinitePlace K // v.IsReal}) :
      IsRealAdditiveComponent (standardGlobalAdditiveCharacter K) v.1 v.2 1 :=
    standardGlobalAdditiveCharacter_isRealComponent K v.1 v.2
  have hStdC (v : {v : NumberField.InfinitePlace K // v.IsComplex}) :
      IsComplexAdditiveComponent (standardGlobalAdditiveCharacter K) v.1 v.2 1 :=
    standardGlobalAdditiveCharacter_isComplexComponent K v.1 v.2
  have heq := hEq (fun _ => 1) hStdR (fun _ => 1) hStdC dR dR' dRd dRd'
    hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
  let A := archimedeanPairGammaBlocks K dR dR' dC dC'
  let Ad := archimedeanPairGammaBlocks K dRd dRd' dCd dCd'
  let ε : ℂˣ := (∏ v, realPairStandardEpsilon (dR v) (dR' v)) *
    ∏ v, complexPairStandardEpsilon (dC v) (dC' v)
  have eL : (fun z : ℂ => ((gammaProduct A).denominator z)⁻¹) = fun z =>
      (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator z)⁻¹) *
        ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator z)⁻¹ :=
    funext (archimedeanPairGammaBlocks_value K dR dR' dC dC')
  have eLd : (fun z : ℂ => ((gammaProduct Ad).denominator z)⁻¹) = fun z =>
      (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator z)⁻¹) *
        ∏ v, ((complexPairLFactor (dCd v) (dCd' v)).denominator z)⁻¹ :=
    funext (archimedeanPairGammaBlocks_value K dRd dRd' dCd dCd')
  have eε : (fun _ : ℂ => (ε : ℂ)) = fun z =>
      (∏ v, (realPairEpsilon (dR v) (dR' v) 1 (NNReal.sqrt ‖((1 : ℝˣ) : ℝ)‖₊)
          (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (1 : ℝˣ).ne_zero)) z : ℂ)) *
        ∏ v, (complexPairEpsilon (dC v) (dC' v) 1 ‖((1 : ℂˣ) : ℂ)‖₊
          (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) z : ℂ) := by
    funext z
    simpa only [ε, Units.val_mul, Units.coe_prod] using
      (congrArg Units.val (archimedeanPairEpsilon_standard_value K dR dR' dC dC' z)).symm
  refine ⟨c, S, A, Ad, ε, ?_, ?_, fun v hv => (hUnram v hv).2.2, ?_⟩
  · exact archimedeanPairGammaBlocks_count K dR dR' dC dC' _
      (fun v => congrArg₂ (· * ·) (hdR v).1 (hdR' v).1)
      (fun v => congrArg₂ (· * ·) (hdC v).1 (hdC' v).1)
  · exact archimedeanPairGammaBlocks_count K dRd dRd' dCd dCd' _
      (fun v => congrArg₂ (· * ·) (hdRd v).1 (hdRd' v).1)
      (fun v => congrArg₂ (· * ·) (hdCd v).1 (hdCd' v).1)
  · apply hasGlobalEquation_of_completedPairEquation c S hS hSd hS' hSd' hUnram A Ad
    rw [eL, eLd, eε]
    exact heq

end Langlands.BaseChange
