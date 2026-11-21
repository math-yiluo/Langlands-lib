import Langlands.BaseChange.CompletedPairDistinguishedComparison
import Langlands.BaseChange.CompletedPairDistinguishedEulerComparison
import Langlands.BaseChange.StandardCompletedTwistEquation

/-! # The distinguished standard epsilon comparison from completed Hecke twists -/

noncomputable section

set_option autoImplicit false

universe u uQ uI

namespace Langlands.BaseChange

open Automorphic Automorphic.ConstantFunctions Global LocalFactor.Archimedean
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open Global.FunctionalEquationComparison RelativeWeilEngine
open scoped BigOperators

/-- Compare the distinguished epsilon monomials of actual Hecke determinant
 twists and a single upper representation. The supplied global pair theorem
 provides the completed equations. The local hypotheses compare the auxiliary
 factors and give the distinguished forward and dual Euler data. -/
def StandardTwistDistinguishedEpsilonStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{u, uQ} →
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (r : ℕ) (I : Type uI) [Fintype I], Fintype.card I = Module.finrank K L →
    ∀ (v₀ : FinitePlace K) (w₀ : FinitePlace L), placesAbove L v₀ = {w₀} →
    ∀ (T Td : CuspidalOperatorRealization K r) (U Ud : CuspidalOperatorRealization L r),
      Td.realization.IsContragredientOf T.realization → Ud.realization.IsContragredientOf U.realization →
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
      (Q : CuspidalSpectralPresentation.{u, uQ} U) (Qd : CuspidalSpectralPresentation.{u, uQ} Ud)
      (hP : HasIrreducibleAdmissibleComponents P) (hPd : HasIrreducibleAdmissibleComponents Pd)
      (hQ : HasIrreducibleAdmissibleComponents Q) (hQd : HasIrreducibleAdmissibleComponents Qd)
      (χ : I → HeckeCharacter K),
    let C := rankOneSpectralPresentation.{u, uQ} K
    let D := rankOneSpectralPresentation.{u, uQ} L
    let hC := rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} K
    let hD := rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} L
    let Lower := ∀ i, FinitePairFactorChoice (standardGlobalAdditiveCharacter K)
      (P.heckeDeterminantTwist (χ i)) C (Pd.heckeDeterminantTwist (χ i)⁻¹) C
      (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i) hP) hC
      (Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i)⁻¹ hPd) hC
    let Upper := FinitePairFactorChoice (standardGlobalAdditiveCharacter L) Q D Qd D hQ hD hQd hD
    (∀ (cF : Lower) (cE : Upper),
      (∀ i, (cF i).lPolynomial v₀ = 1 ∧ (cF i).dualLPolynomial v₀ = 1) ∧
      (∀ x : ℂ, x ≠ 0 → (cE.lPolynomial w₀).eval x = 0 →
        (cE.dualLPolynomial w₀).eval ((residueCardinality w₀ : ℂ)⁻¹ / x) ≠ 0) ∧
      ∀ v ≠ v₀,
        (∀ z, (∏ i, (cF i).finiteL v z) = ∏ w ∈ placesAbove L v, cE.finiteL w z) ∧
        (∀ z, (∏ i, (cF i).finiteDualL v z) = ∏ w ∈ placesAbove L v, cE.finiteDualL w z) ∧
        finiteEpsilonBase Finset.univ (fun _ : I => residueCardinality v) (fun i => (cF i).epsilon v) =
          finiteEpsilonBase (placesAbove L v) residueCardinality cE.epsilon) →
    ∃ (cF : Lower) (cE : Upper),
      EpsilonMonomialProductComparison (residueCardinality v₀) (residueCardinality w₀)
        Finset.univ (fun i => (cF i).epsilon v₀) (cE.epsilon w₀)

set_option maxHeartbeats 2400000 in
/-- Choose the actual completed equations, compare both distinguished polynomials,
then cancel gamma counts and the auxiliary epsilon bases. -/
theorem standardTwistDistinguishedEpsilon : StandardTwistDistinguishedEpsilonStatement.{u, uQ, uI} := by
  classical
  intro hFE K L _ _ _ _ _ _ _ r I _ hI v₀ w₀ hw T Td U Ud hTd hUd
    P Pd Q Qd hP hPd hQ hQd χ C D hC hD Lower Upper hlocal
  choose cF SF AF AdF εF hAF hAdF hSF hF using fun i =>
    standardCompletedTwistEquation hFE K r T Td hTd P Pd hP hPd (χ i)
  obtain ⟨cE, SE, AE, AdE, εE, hAE, hAdE, hSE, hE⟩ :=
    standardCompletedPairEquation hFE L r 0 U Ud (rankOneCuspidal L) (rankOneCuspidal L) hUd
      (rankOneCuspidal_isContragredientOf_self L) Q D Qd D hQ hD hQd hD
  obtain ⟨h₀, hsep, haux⟩ := hlocal cF cE
  let Pχ := fun i => P.heckeDeterminantTwist (χ i)
  let Pdχ := fun i => Pd.heckeDeterminantTwist (χ i)⁻¹
  let hPχ := fun i => P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i) hP
  let hPdχ := fun i => Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i)⁻¹ hPd
  obtain ⟨h₀E, hd₀E⟩ := completedPairDistinguishedEulerComparison K L r 0 I v₀ w₀ hw
    _ _ _ _ U Ud (rankOneCuspidal L) (rankOneCuspidal L) Pχ (fun _ => C) Pdχ (fun _ => C) Q D Qd D
    hPχ (fun _ => hC) hPdχ (fun _ => hC) hQ hD hQd hD cF cE SF SE AF AdF AE AdE εF εE
    hSF hF hE h₀ (fun v hv => (haux v hv).1) (fun v hv => (haux v hv).2.1) hsep
  have hL : ∀ v z, (∏ i, (cF i).finiteL v z) = ∏ w ∈ placesAbove L v, cE.finiteL w z := by
    intro v z
    by_cases hv : v = v₀
    · subst v
      rw [hw, Finset.prod_singleton]
      simp only [FinitePairFactorChoice.finiteL, h₀E, (fun i => (h₀ i).1), Polynomial.eval_one,
        inv_one, Finset.prod_const_one]
    · exact (haux v hv).1 z
  have hdL : ∀ v z, (∏ i, (cF i).finiteDualL v z) = ∏ w ∈ placesAbove L v, cE.finiteDualL w z := by
    intro v z
    by_cases hv : v = v₀
    · subst v
      rw [hw, Finset.prod_singleton]
      simp only [FinitePairFactorChoice.finiteDualL, hd₀E, (fun i => (h₀ i).2), Polynomial.eval_one,
        inv_one, Finset.prod_const_one]
    · exact (haux v hv).2.1 z
  refine ⟨cF, cE, ?_⟩
  exact completedPairDistinguishedComparison K L r 0 I hI v₀ w₀ hw
    _ _ _ _ U Ud (rankOneCuspidal L) (rankOneCuspidal L) Pχ (fun _ => C) Pdχ (fun _ => C) Q D Qd D
    hPχ (fun _ => hC) hPdχ (fun _ => hC) hQ hD hQd hD cF cE SF SE AF AdF AE AdE εF εE
    hSF hSE hF hE
    (by simpa only [Nat.zero_add, mul_one] using hAF) (by simpa only [Nat.zero_add, mul_one] using hAdF)
    hAE hAdE hL hdL (fun v hv => (haux v hv).2.2)

end Langlands.BaseChange
