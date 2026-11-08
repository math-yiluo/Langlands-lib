import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement
import Langlands.Representation.RankinSelberg.TemperedLFactorStatement
import Langlands.Representation.RankinSelberg.SegmentPairPoleOrder
import Langlands.Representation.RankinSelberg.UnramifiedTwistLFactorProof
import Langlands.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.Representation.Induction.BlockEquivalence

/-! # Common real twists in the tempered block product formula -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Polynomial

universe uF uV uW uV' uW'

variable {p : ℕ} [Fact p.Prime]

section CommonTwists

variable (F : PadicField.{uF} p)

local instance groupedLFactorReductionTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- The substitution on denominator polynomials for a real unramified twist. -/
def realTwistPolynomial (s : ℝ) : ℂ[X] →+* ℂ[X] :=
  compRingHom (C ((F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-(s : ℂ))) * X)

/-- The smooth character `x ↦ |x|^s` of the multiplicative group. -/
def realTwistCharacter (s : ℝ) : Induction.SmoothCharacter ℂ F.Carrierˣ :=
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  ⟨realPowerCharacter F.canonicalTopologicalData.normalizedAbsUnits s,
    isOpen_ker_realPowerCharacter _
      F.canonicalTopologicalData.isOpen_ker_normalizedAbsUnits s⟩

theorem realTwistCharacter_spec (s : ℝ) (x : F.Carrierˣ) :
    ((realTwistCharacter F s).toMonoidHom x : ℂ) =
      (F.canonicalTopologicalData.normalizedAbs x : ℂ) ^ (s : ℂ) := by
  change ((F.canonicalTopologicalData.normalizedAbs x ^ s : ℝ) : ℂ) = _
  exact Complex.ofReal_cpow (F.canonicalTopologicalData.normalizedAbs_nonneg _) _

theorem realTwistCharacter_comp (s : ℝ) (n : ℕ) :
    (realTwistCharacter F s).toMonoidHom.comp
        (determinant : GeneralLinear n F.Carrier →* F.Carrierˣ) =
      F.canonicalTopologicalData.determinantPowerCharacter n s := rfl

/-- The closed twist theorem acts on real-power twists in both variables. -/
theorem IsPadicRankLPolynomial.twist_real
    {n t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear t F.Carrier) W}
    {P : ℂ[X]} (hP : IsPadicRankLPolynomial F ψ ν.val π σ P) (s z : ℝ) :
    IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) s π)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm t) z σ)
      (realTwistPolynomial F z (realTwistPolynomial F s P)) := by
  cases n with
  | zero => exact False.elim hP
  | succ n =>
    cases t with
    | zero => exact False.elim hP
    | succ t =>
      have h₁ := (unramifiedTwistLFactor p F ψ ν n t π σ
        (s : ℂ) (realTwistCharacter F s).toMonoidHom
        (realTwistCharacter_spec F s) P hP).2
      have h₂ := (unramifiedTwistLFactor p F ψ ν n t
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n + 1)) s π) σ
        (z : ℂ) (realTwistCharacter F z).toMonoidHom
        (realTwistCharacter_spec F z) _ h₁).1
      exact h₂

/-- Proposition (8.4), with arbitrary positive block sizes in place of
syntactically successor sizes. The analytic product theorem remains a premise. -/
theorem TemperedLFactorStatement.blockShape
    (H : TemperedLFactorStatement.{uF, uV, uW})
    {r t : ℕ} (B : BlockShape (r + 1)) (C : BlockShape (t + 1))
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin C.length → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (σ : ∀ j, Representation ℂ (GeneralLinear (C.size j) F.Carrier) (W j))
    (hiπ : ∀ i, Representation.IsIrreducible (π i))
    (hsπ : ∀ i, F.canonicalTopologicalData.IsSquareIntegrable (π i))
    (hiσ : ∀ j, Representation.IsIrreducible (σ j))
    (hsσ : ∀ j, F.canonicalTopologicalData.IsSquareIntegrable (σ j)) :
    ∃ (P : ℂ[X]) (Q : Fin B.length → Fin C.length → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val
        (F.canonicalNormalizedProductInduced B π)
        (F.canonicalNormalizedProductInduced C σ) P ∧
      (∀ i j, IsPadicRankLPolynomial F ψ ν.val (π i) (σ j) (Q i j)) ∧
      P = ∏ i, ∏ j, Q i j := by
  classical
  rcases B with ⟨k, m, hmpos, hm⟩
  rcases C with ⟨l, n, hnpos, hn⟩
  choose m' hm' using fun i => Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hmpos i))
  choose n' hn' using fun j => Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hnpos j))
  have hmfun : m = fun i => m' i + 1 := funext hm'
  have hnfun : n = fun j => n' j + 1 := funext hn'
  subst m n
  obtain ⟨P, Q, hP, hQ, hprod, -⟩ := H p F ψ ν r t k l m' n' hm hn π σ
    hiπ hsπ hiσ hsσ
  exact ⟨P, Q, hP, hQ, hprod⟩

/-- Common real twists on the two induced square-integrable families preserve
the product formula. Both twists are applied to the denominator polynomials. -/
theorem TemperedLFactorStatement.commonRealTwists
    (H : TemperedLFactorStatement.{uF, uV, uW})
    {r t : ℕ} (B : BlockShape (r + 1)) (C : BlockShape (t + 1))
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin C.length → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (σ : ∀ j, Representation ℂ (GeneralLinear (C.size j) F.Carrier) (W j))
    (hiπ : ∀ i, Representation.IsIrreducible (π i))
    (hsπ : ∀ i, F.canonicalTopologicalData.IsSquareIntegrable (π i))
    (hiσ : ∀ j, Representation.IsIrreducible (σ j))
    (hsσ : ∀ j, F.canonicalTopologicalData.IsSquareIntegrable (σ j))
    (s z : ℝ) :
    ∃ (P : ℂ[X]) (Q : Fin B.length → Fin C.length → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val
        (F.canonicalNormalizedProductInduced B
          (fun i => realPowerTwist (F.canonicalTopologicalData.determinantNorm (B.size i))
            s (π i)))
        (F.canonicalNormalizedProductInduced C
          (fun j => realPowerTwist (F.canonicalTopologicalData.determinantNorm (C.size j))
            z (σ j))) P ∧
      (∀ i j, IsPadicRankLPolynomial F ψ ν.val
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (B.size i)) s (π i))
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (C.size j)) z (σ j))
        (Q i j)) ∧
      P = ∏ i, ∏ j, Q i j := by
  obtain ⟨P, Q, hP, hQ, hprod⟩ := H.blockShape F ψ ν B C π σ hiπ hsπ hiσ hsσ
  let S := realTwistPolynomial F s
  let Z := realTwistPolynomial F z
  refine ⟨Z (S P), fun i j => Z (S (Q i j)), ?_, ?_, ?_⟩
  · have htw := IsPadicRankLPolynomial.twist_real F ψ ν (n := r + 1) (t := t + 1) hP s z
    exact (IsPadicSymmetricLPolynomial.congr_equiv
      (F.canonicalTopologicalData.normalizedProductDeterminantTwistEquiv B
        (realTwistCharacter F s) π)
      (F.canonicalTopologicalData.normalizedProductDeterminantTwistEquiv C
        (realTwistCharacter F z) σ)).mp htw
  · intro i j
    exact (hQ i j).twist_real F ψ ν s z
  · rw [hprod, map_prod, map_prod]
    simp only [map_prod]

end CommonTwists

end Langlands.RankinSelberg
