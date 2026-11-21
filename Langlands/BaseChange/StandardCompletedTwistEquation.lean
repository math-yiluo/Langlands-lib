import Langlands.Automorphic.ConstantUnitaryForm
import Langlands.Automorphic.CuspidalInvariantPairingCriterion
import Langlands.Automorphic.Unramified.CuspidalPowerTraceIndependenceReduction
import Langlands.BaseChange.SphericalStandardFactorsAtCompletion
import Langlands.BaseChange.StandardCompletedPairEquation

/-! # Completed standard equations for a cuspidal Hecke twist -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Automorphic.ConstantFunctions

open Global

variable (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual cuspidal line of constant functions on `GL₁` is its own contragredient. -/
theorem rankOneCuspidal_isContragredientOf_self :
    (rankOneCuspidal K).realization.IsContragredientOf (rankOneCuspidal K).realization := by
  let e := scalarEquiv K 1
  let B : (realization K 1).Space →ₗ[ℂ] (realization K 1).Space →ₗ[ℂ] ℂ :=
    (LinearMap.mul ℂ ℂ).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
  have hI : (realization K 1).IsInvariantPairing (realization K 1) B := by
    refine ⟨?_, ?_, ?_⟩
    · intro g y x
      have hfix (f : (realization K 1).Space) :
          (realization K 1).finiteRepresentation g f = f :=
        (e.surjective.forall (p := fun z => (realization K 1).finiteRepresentation g z = z)).mpr
          (finiteRepresentation_scalarEquiv K 1 g) f
      exact congrArg₂ (fun f h => B f h) (hfix y) (hfix x)
    · intro k y x
      have hfix (f : (realization K 1).Space) :
          (realization K 1).compactRepresentation k f = f :=
        (e.surjective.forall (p := fun z => (realization K 1).compactRepresentation k z = z)).mpr
          (compactRepresentation_scalarEquiv K 1 k) f
      exact congrArg₂ (fun f h => B f h) (hfix y) (hfix x)
    · intro X y x
      have hzero (f : (realization K 1).Space) :
          (realization K 1).lieAction X f = 0 := realGenerator_eq_zero K 1 X f
      rw [hzero y, hzero x]
      simp only [map_zero, LinearMap.zero_apply, add_zero]
  have hB0 : B ≠ 0 := by
    have hB : B (e 1) (e 1) = 1 := by
      change e.symm (e 1) * e.symm (e 1) = 1
      rw [e.symm_apply_apply, one_mul]
    intro h
    have hz := LinearMap.congr_fun (LinearMap.congr_fun h (e 1)) (e 1)
    exact one_ne_zero (by simpa only [hB, LinearMap.zero_apply] using hz)
  exact CuspidalOperatorRealization.isContragredientOf_of_nonzero_invariant
    (S := rankOneCuspidal K) (T := rankOneCuspidal K) hI hB0

end Langlands.Automorphic.ConstantFunctions

namespace Langlands.BaseChange

open Automorphic Automorphic.ConstantFunctions Global LocalFactor.Archimedean
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open Global.FunctionalEquationComparison.RelativeWeilEngine

/-- Choose a contragredient with actual irreducible admissible finite components
in the requested presentation universe. -/
theorem exists_cuspidalContragredient_presentation
    (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    {r : ℕ} (T : CuspidalOperatorRealization K r) :
    ∃ (Td : CuspidalOperatorRealization K r) (Pd : CuspidalSpectralPresentation.{u, uQ} Td),
      Td.realization.IsContragredientOf T.realization ∧ HasIrreducibleAdmissibleComponents Pd := by
  obtain ⟨Td, hTd⟩ := cuspidalContragredientExistence K r T
  obtain ⟨A, hI, hA⟩ := cuspidalIrreducibleAdmissibleFiniteSliceExistence K r Td
  obtain ⟨P, hP⟩ := Td.exists_presentation_of_finiteSlice A hI hA
  obtain ⟨Pd, hPd⟩ := P.exists_small hP
  exact ⟨Td, Pd, hTd, hPd⟩

/-- The completed standard equation of an actual Hecke determinant twist. Its
second member is the constant cuspidal line and its first dual member is the
inverse twist of the supplied contragredient. -/
def StandardCompletedTwistEquationStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{u, uQ} →
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T Td : CuspidalOperatorRealization K r),
    Td.realization.IsContragredientOf T.realization →
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
      (h : HasIrreducibleAdmissibleComponents P) (hd : HasIrreducibleAdmissibleComponents Pd)
      (χ : HeckeCharacter K),
      let C := rankOneSpectralPresentation.{u, uQ} K
      let hC := rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} K
      ∃ (c : FinitePairFactorChoice (standardGlobalAdditiveCharacter K) (P.heckeDeterminantTwist χ)
          C (Pd.heckeDeterminantTwist χ⁻¹) C
          (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ h) hC
          (Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ⁻¹ hd) hC)
        (S : Finset (FinitePlace K)) (A Ad : List GammaBlock) (ε : ℂˣ),
        ((A.flatMap GammaBlock.realShifts).length = Module.finrank ℚ K * (r + 1)) ∧
        ((Ad.flatMap GammaBlock.realShifts).length = Module.finrank ℚ K * (r + 1)) ∧
        (∀ v ∉ S, c.epsilon v = (1, 0)) ∧
        HasGlobalEquation c.finiteL c.finiteDualL c.finiteEpsilon
          (fun z => ((gammaProduct A).denominator z)⁻¹)
          (fun z => ((gammaProduct Ad).denominator z)⁻¹) (fun _ => (ε : ℂ)) S

set_option maxHeartbeats 1800000 in
/-- Use the standard completed pair equation for the twisted presentations and the
actual self-dual constant presentation. -/
theorem standardCompletedTwistEquation : StandardCompletedTwistEquationStatement.{u, uQ} := by
  intro hFE K _ _ _ r T Td hD P Pd h hd χ C hC
  have hDχ : (Td.heckeDeterminantTwist χ⁻¹).realization.IsContragredientOf
      (T.heckeDeterminantTwist χ).realization := hD.heckeDeterminantTwist_inv χ
  simpa only [Nat.zero_add, mul_one] using
    standardCompletedPairEquation hFE K r 0 (T.heckeDeterminantTwist χ) (Td.heckeDeterminantTwist χ⁻¹)
      (rankOneCuspidal K) (rankOneCuspidal K) hDχ (rankOneCuspidal_isContragredientOf_self K)
      (P.heckeDeterminantTwist χ) C (Pd.heckeDeterminantTwist χ⁻¹) C
      (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ h) hC
      (Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ⁻¹ hd) hC

end Langlands.BaseChange
