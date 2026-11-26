import Langlands.Automorphic.AssociatedGammaAutomorphicFamily
import Langlands.Global.Factors.CuspidalPairLocalDataProof
import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalTCReduction
import Langlands.Global.Factors.CuspidalSatakeBoundReduction
import Langlands.Global.RankinSelberg.EqualAnalyticProof
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualUnfoldingProof

/-! # Functional-equation inputs for determinant twists of equal-rank pairs -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalPairFunctionalEquation

open NumberField HeckeFunctionalEquation FunctionalEquationComparison
open FunctionalEquationComparison.CompletedEquationAdapter
open CuspidalPairPartialGammaGlobal RankinSelbergGlobal
open CompletionPadic Automorphic
open scoped Classical

namespace AutomorphicTwistSetup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {r t : ℕ}

/-- For every determinant twist trivial at infinity, the Euler family satisfies the
functional-equation inputs on every enlargement of some finite exceptional set. -/
def HasEngineInputs (D : AutomorphicTwistSetup.{u, uQ} ψ r t) : Prop :=
  ∀ (χ : HeckeCharacter F), χ.HasPrescribedInfinityComponent 1 →
    ∃ S : Finset (FinitePlace F), ∀ B : Finset (FinitePlace F), S ⊆ B →
      HeckeEulerFamily.HasEngineInputs (D.localFactors χ) B

/-- Specialize the completed equation to the twists of the supplied pair. -/
theorem hasEngineInputs_of_globalEquation
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t)
    (hFE : CuspidalPairGlobalFunctionalEquationStatement.{u, uQ})
    (hψ : ∃ x : Adeles F, ψ x ≠ 1) (hdiag : ∀ x : F, ψ (diagonal F x) = 1) :
    D.HasEngineInputs := by
  intro χ hχ
  obtain ⟨S, -, hS⟩ := D.exists_engineInputs hFE hψ hdiag χ hχ
  exact ⟨S, hS⟩

set_option maxHeartbeats 2500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem hasEngineInputs_of_equalPackage
    (D : AutomorphicTwistSetup.{u, uQ} ψ r r) (hEq : EqualPackageAt.{u, uQ} F)
    (hψ : ∃ x : Adeles F, ψ x ≠ 1) (hdiag : ∀ x : F, ψ (diagonal F x) = 1) :
    D.HasEngineInputs := by
  classical
  intro χ hχ
  let T := D.T.heckeDeterminantTwist χ
  let Td := D.Td.heckeDeterminantTwist χ⁻¹
  let P := D.P.heckeDeterminantTwist χ
  let Pd := D.Pd.heckeDeterminantTwist χ⁻¹
  let hP := D.P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ D.h
  let hPd := D.Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ⁻¹ D.hd
  have hTd : Td.realization.IsContragredientOf T.realization :=
    OperatorRealization.IsContragredientOf.heckeDeterminantTwist_inv D.hTd χ
  obtain ⟨-, -, -, S, hS₁, hS₂, hS₃, hS₄, hSψ, hChoice⟩ :=
    cuspidalPairLocalData F ψ hψ hdiag r r T Td D.T' D.Td' hTd D.hTd' P D.P' Pd D.Pd'
      hP D.h' hPd D.hd'
  let c := D.twistedChoice χ
  have hunr := hChoice c
  have hχi := HeckeCharacter.hasPrescribedInfinityComponent_one_inv hχ
  obtain ⟨_, _, _, _, _, hI, hJ, hA, hB, hA₀, hB₀, hIJ, hf, hfd, hsem⟩ :=
    hEq ψ hdiag r T Td D.T' D.Td' hTd D.hTd' P D.P' Pd D.Pd' hP D.h'
      S hS₁ hS₂ hS₃ hS₄ hSψ D.aR D.aR_spec D.aC D.aC_spec D.dR D.dR' D.dRd D.dRd'
      (fun v => OperatorRealization.HasRealPlaceParameter.heckeDeterminantTwist _ hχ (D.dR_spec v))
      D.dR'_spec
      (fun v => OperatorRealization.HasRealPlaceParameter.heckeDeterminantTwist _ hχi (D.dRd_spec v))
      D.dRd'_spec D.dC D.dC' D.dCd D.dCd'
      (fun v => OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist _ hχ (D.dC_spec v))
      D.dC'_spec
      (fun v => OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist _ hχi (D.dCd_spec v))
      D.dCd'_spec
  have hL : MeromorphicOn D.infiniteL Set.univ :=
    fun s _ => (cuspidalInfiniteL_spec D.dR D.dR' D.dC D.dC').1.1 s
  have hLd : MeromorphicOn D.dualInfiniteL Set.univ :=
    fun s _ => (cuspidalInfiniteL_spec D.dRd D.dRd' D.dCd D.dCd').1.1 s
  obtain ⟨_, _, hΛ, hΛd, hprod, hprodd, hFE⟩ :=
    exists_partialEquation hL hLd hI hJ hA hB hA₀ hB₀ hIJ hf hfd
  let G (v : FinitePlace F) : RankinSelberg.RationalFunctions :=
    RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection (padicField v))
      (c.epsilon v).1 (c.epsilon v).2 (c.lPolynomial v) (c.dualLPolynomial v)
  let gamma (v : FinitePlace F) (s : ℂ) : ℂ :=
    RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)
  specialize hsem c.additive c.additive_spec c.measure c.measure_spec G
  have hGamma := fun v (_ : v ∈ S) => c.isPadicSymmetricGammaFactor hTd D.hTd' v
  have hsemintegral := hsem hGamma
  have hfe := hFE (fun s => (∏ v ∈ S, gamma v s) * D.infiniteEpsilon s) hsemintegral
  have hcont := c.continuationHolds_of_partialGamma hS₁ hS₂ hS₃ hS₄ hunr
    hΛ hΛd hprod hprodd gamma hfe (fun v _ => c.eventually_finiteL_mul_gamma v)
  have hSat := cuspidalSatakeBoundReduction.{u, uQ} OperatorRealization.irreducibleCentralCharacter
  obtain ⟨C₁, hC₁⟩ := hSat F r T P hP
  obtain ⟨C₂, hC₂⟩ := hSat F r D.T' D.P' D.h'
  obtain ⟨C₃, hC₃⟩ := hSat F r Td Pd hPd
  obtain ⟨C₄, hC₄⟩ := hSat F r D.Td' D.Pd' D.hd'
  have hCompleted := c.completedEquationHolds_of_continuationHolds hS₁ hS₂ hS₃ hS₄
    hunr hC₁ hC₂ hC₃ hC₄ hcont
  refine ⟨S, fun B hSB => ?_⟩
  obtain ⟨σ', Lp, Lpd, hA', hE, hF⟩ := c.exists_engineInputs_cuspidal S B hSB hunr D.aR D.aC
    D.dR D.dR' D.dRd D.dRd' D.dC D.dC' D.dCd D.dCd' hCompleted D.w₀
  exact ⟨σ', Lp, Lpd, hA', hE, hF⟩

end AutomorphicTwistSetup

/-- Functional-equation inputs for determinant twists of actual equal-rank cuspidal
pairs at the given field. -/
def EqualRankTwistEngineInputsAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∃ x : Adeles F, ψ x ≠ 1) → (∀ x : F, ψ (diagonal F x) = 1) →
    ∀ (r : ℕ) (D : AutomorphicTwistSetup.{u, uQ} ψ r r), D.HasEngineInputs

/-- Functional-equation inputs for the family of determinant twists of every actual
equal-rank cuspidal pair. -/
def EqualRankTwistEngineInputsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
    EqualRankTwistEngineInputsAt.{u, uQ} F

/-- The completed global pair equation gives the required equal-rank inputs. -/
theorem equalRankTwistEngineInputs_of_globalEquation
    (hFE : CuspidalPairGlobalFunctionalEquationStatement.{u, uQ}) :
    EqualRankTwistEngineInputsStatement.{u, uQ} := by
  intro F _ _ _ ψ hψ hdiag r D
  exact D.hasEngineInputs_of_globalEquation hFE hψ hdiag

/-- The equal-rank semi-local equation suffices for the equal-rank twist inputs. -/
def EqualRankTwistEngineInputsFromSemilocalStatement : Prop :=
  EqualSemilocalEquationStatement.{u, uQ} → EqualRankTwistEngineInputsStatement.{u, uQ}

theorem equalRankTwistEngineInputs_of_semilocalEquation :
    EqualRankTwistEngineInputsFromSemilocalStatement.{u, uQ} := by
  intro hS F _ _ _ ψ hψ hdiag r D
  have hEq := equalPackage EqualAnalytic.equalAnalyticStatement_proof equalUnfoldingStatement_proof
    equalEulerFactorization equalDualEulerFactorization hS
  exact D.hasEngineInputs_of_equalPackage (hEq F) hψ hdiag

/-- The totally complex semi-local equation suffices for the same twist inputs at any
supplied totally complex field. -/
theorem equalRankTwistEngineInputsAt_of_semilocalEquationTC
    (hS : EqualSemilocalEquationTCStatement.{u, uQ})
    (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)] : EqualRankTwistEngineInputsAt.{u, uQ} F := by
  intro ψ hψ hdiag r D
  have hEq := CuspidalPairPartialGammaTC.equalPackageTC EqualAnalytic.equalAnalyticStatement_proof
    equalUnfoldingStatement_proof equalEulerFactorization equalDualEulerFactorization hS
  exact D.hasEngineInputs_of_equalPackage (hEq F) hψ hdiag

end Langlands.Global.CuspidalPairFunctionalEquation
