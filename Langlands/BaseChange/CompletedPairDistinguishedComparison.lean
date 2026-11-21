import Langlands.BaseChange.DistinguishedPlaceComparisonFromEquations
import Langlands.BaseChange.StandardArchimedeanComparison
import Langlands.Automorphic.AssociatedAdditiveInputs
import Langlands.Global.Factors.RelativeWeilAssemblyHecke
import Langlands.Global.Factors.CuspidalPairResidueCardinality

/-! # Comparison of completed pair equations at a distinguished completion -/

noncomputable section

set_option autoImplicit false

universe u uQ uX

open scoped BigOperators NumberField

namespace Langlands.BaseChange

open Global Automorphic IsDedekindDomain LocalFactor.Archimedean RankinSelberg
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open Global.FunctionalEquationComparison RelativeWeilEngine

/-- At a place with one place above, compare the local epsilon monomials of a family
of standard completed pair equations and an upper pair equation. The two finite
Euler comparisons and the auxiliary epsilon bases are the local inputs. -/
def CompletedPairDistinguishedComparisonStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (r t : ℕ) (I : Type uX) [Fintype I], Fintype.card I = Module.finrank K L →
    ∀ (v₀ : FinitePlace K) (w₀ : FinitePlace L), placesAbove L v₀ = {w₀} →
    ∀ (T Td : I → CuspidalOperatorRealization K r) (T' Td' : I → CuspidalOperatorRealization K t)
      (U Ud : CuspidalOperatorRealization L r) (U' Ud' : CuspidalOperatorRealization L t)
      (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
      (P' : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T' i))
      (Pd : ∀ i, CuspidalSpectralPresentation.{u, uQ} (Td i))
      (Pd' : ∀ i, CuspidalSpectralPresentation.{u, uQ} (Td' i))
      (Q : CuspidalSpectralPresentation.{u, uQ} U) (Q' : CuspidalSpectralPresentation.{u, uQ} U')
      (Qd : CuspidalSpectralPresentation.{u, uQ} Ud) (Qd' : CuspidalSpectralPresentation.{u, uQ} Ud')
      (hP : ∀ i, HasIrreducibleAdmissibleComponents (P i))
      (hP' : ∀ i, HasIrreducibleAdmissibleComponents (P' i))
      (hPd : ∀ i, HasIrreducibleAdmissibleComponents (Pd i))
      (hPd' : ∀ i, HasIrreducibleAdmissibleComponents (Pd' i))
      (hQ : HasIrreducibleAdmissibleComponents Q) (hQ' : HasIrreducibleAdmissibleComponents Q')
      (hQd : HasIrreducibleAdmissibleComponents Qd) (hQd' : HasIrreducibleAdmissibleComponents Qd')
      (cF : ∀ i, FinitePairFactorChoice (standardGlobalAdditiveCharacter K) (P i) (P' i) (Pd i) (Pd' i)
        (hP i) (hP' i) (hPd i) (hPd' i))
      (cE : FinitePairFactorChoice (standardGlobalAdditiveCharacter L) Q Q' Qd Qd' hQ hQ' hQd hQd')
      (SF : I → Finset (FinitePlace K)) (SE : Finset (FinitePlace L))
      (AF AdF : I → List GammaBlock) (AE AdE : List GammaBlock) (εF : I → ℂˣ) (εE : ℂˣ),
      (∀ i v, v ∉ SF i → (cF i).epsilon v = (1, 0)) →
      (∀ w ∉ SE, cE.epsilon w = (1, 0)) →
      (∀ i, HasGlobalEquation (cF i).finiteL (cF i).finiteDualL (cF i).finiteEpsilon
        (fun z => ((gammaProduct (AF i)).denominator z)⁻¹)
        (fun z => ((gammaProduct (AdF i)).denominator z)⁻¹) (fun _ => (εF i : ℂ)) (SF i)) →
      HasGlobalEquation cE.finiteL cE.finiteDualL cE.finiteEpsilon
        (fun z => ((gammaProduct AE).denominator z)⁻¹)
        (fun z => ((gammaProduct AdE).denominator z)⁻¹) (fun _ => (εE : ℂ)) SE →
      (∀ i, ((AF i).flatMap GammaBlock.realShifts).length = Module.finrank ℚ K * ((r + 1) * (t + 1))) →
      (∀ i, ((AdF i).flatMap GammaBlock.realShifts).length = Module.finrank ℚ K * ((r + 1) * (t + 1))) →
      (AE.flatMap GammaBlock.realShifts).length = Module.finrank ℚ L * ((r + 1) * (t + 1)) →
      (AdE.flatMap GammaBlock.realShifts).length = Module.finrank ℚ L * ((r + 1) * (t + 1)) →
      (∀ v z, (∏ i, (cF i).finiteL v z) = ∏ w ∈ placesAbove L v, cE.finiteL w z) →
      (∀ v z, (∏ i, (cF i).finiteDualL v z) = ∏ w ∈ placesAbove L v, cE.finiteDualL w z) →
      (∀ v ≠ v₀, finiteEpsilonBase Finset.univ (fun _ : I => residueCardinality v)
        (fun i => (cF i).epsilon v) = finiteEpsilonBase (placesAbove L v) residueCardinality cE.epsilon) →
      EpsilonMonomialProductComparison (residueCardinality v₀) (residueCardinality w₀)
        Finset.univ (fun i => (cF i).epsilon v₀) (cE.epsilon w₀)

set_option maxHeartbeats 1800000 in
/-- Combine the exceptional sets after projecting the upper places down. The equations
can be enlarged to these sets because the added finite factors are one. Use the degree
formula for both Gamma counts and compare the two constant archimedean epsilon units. -/
theorem completedPairDistinguishedComparison : CompletedPairDistinguishedComparisonStatement.{u, uQ, uX} := by
  classical
  intro K L _ _ _ _ _ _ _ r t I _ hI v₀ w₀ hw T Td T' Td' U Ud U' Ud' P P' Pd Pd' Q Q' Qd Qd'
    hP hP' hPd hPd' hQ hQ' hQd hQd' cF cE SF SE AF AdF AE AdE εF εE hSF hSE hF hE
    hAF hAdF hAE hAdE hEuler hDual hLocal
  let under (w : FinitePlace L) : FinitePlace K := w.under (𝓞 K)
  let S := insert v₀ (Finset.univ.biUnion SF ∪ SE.image under)
  have hv : v₀ ∈ S := Finset.mem_insert_self _ _
  have hsubF (i : I) : SF i ⊆ S := fun _ hv => Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩))
  have hsubE : SE ⊆ S.biUnion (placesAbove L) := fun w hw => Finset.mem_biUnion.mpr
    ⟨under w, Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem under hw)),
      (mem_placesAbove w (under w)).mpr rfl⟩
  have hF' (i : I) := (hF i).changeSet (T' := S) (fun v hv hn => False.elim (hn (hsubF i hv)))
    (fun v _ hn z => by simp [FinitePairFactorChoice.finiteEpsilon, hSF i v hn])
  have hE' := hE.changeSet (T' := S.biUnion (placesAbove L))
    (fun w hw hn => False.elim (hn (hsubE hw)))
    (fun w _ hn z => by simp [FinitePairFactorChoice.finiteEpsilon, hSE w hn])
  have hArch : ∃ c : ℂˣ, ∀ z : ℂ, (∏ i : I, (εF i : ℂ)) = (c : ℂ) * (εE : ℂ) ∧ (εE : ℂ) ≠ 0 := by
    refine ⟨(∏ i : I, εF i) * εE⁻¹, fun _ => ⟨?_, εE.ne_zero⟩⟩
    rw [← Units.coe_prod, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc,
      inv_mul_cancel₀ εE.ne_zero, mul_one]
  have hcard : (Finset.univ : Finset I).card = Module.finrank K L := by simpa using hI
  exact distinguishedPlaceComparisonFromEquations (FinitePlace K) (FinitePlace L) I Finset.univ S
    v₀ w₀ (placesAbove L) under hv mem_placesAbove hw residueCardinality residueCardinality
    (fun v => Nat.zero_lt_one.trans (FinitePairFactorChoice.one_lt_residueCardinality v))
    (fun w => Nat.zero_lt_one.trans (FinitePairFactorChoice.one_lt_residueCardinality w))
    (fun i => (cF i).epsilon) cE.epsilon (fun i => (cF i).finiteL) (fun i => (cF i).finiteDualL)
    cE.finiteL cE.finiteDualL AF AdF AE AdE (fun i _ => (εF i : ℂ)) (fun _ => (εE : ℂ))
    (fun i _ => hF' i) hE' hEuler hDual
    (archimedeanPairGammaCountComparison K L I Finset.univ hcard _ AF AE (fun i _ => hAF i) hAE)
    (archimedeanPairGammaCountComparison K L I Finset.univ hcard _ AdF AdE (fun i _ => hAdF i) hAdE)
    hArch (fun v hv => hLocal v (Finset.mem_erase.mp hv).1)

end Langlands.BaseChange
