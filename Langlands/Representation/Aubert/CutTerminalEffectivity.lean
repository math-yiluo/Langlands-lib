import Langlands.Representation.Aubert.CutEulerExpansion
import Langlands.Representation.Aubert.RankZero
import Langlands.Representation.Smooth.FiniteExactEuler

/-! Actual terminal quotients and their common-sign Aubert classes. -/

noncomputable section

namespace Langlands.Aubert.ActualCutComplex

open CategoryTheory GeneralLinear SmoothRep
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ}

/-- The differential between the unchanged actual finite-length degrees. -/
def finiteDifferential :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.HasFiniteLength) (k : ℕ),
      (finiteDegree.{uF,uV} F T A hA k).val ⟶
        (finiteDegree.{uF,uV} F T A hA (k + 1)).val :=
  letI := T.topology
  fun A _ k => degreeMorphism T A.representation k

/-- The actual quotient of degree `m` by the incoming differential, retaining
degree zero itself when `m = 0`. -/
def terminalObject :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
      A.HasFiniteLength → ℕ →
        FiniteLengthObject.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  fun A hA m => FiniteExactEuler.terminal
    (finiteDegree.{uF,uV} F T A hA) (finiteDifferential.{uF,uV} F T A hA) m

/-- Concrete concentration conditions on the actual cut complex: exactness
before `m` and zero degree carriers above `m`. -/
def ConcentratedAt :
    letI := T.topology
    ∀ (_A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
      ℕ → Prop :=
  letI := T.topology
  fun A m =>
    (0 < m → Function.Injective (differential T A.representation 0)) ∧
    (∀ i, i + 1 < m →
      LinearMap.range (differential T A.representation i).toLinearMap =
        LinearMap.ker (differential T A.representation (i + 1)).toLinearMap) ∧
    (∀ k, m < k → Subsingleton ((diagram T A.representation).Degree k))

/-- Zero carriers above `m` truncate the actual Aubert expansion at `m`. -/
theorem alternating_truncated_expansion (m : ℕ) (hm : m + 1 ≤ n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.HasFiniteLength),
      (∀ k, m < k → Subsingleton ((diagram T A.representation).Degree k)) →
      alternatingOperator.{uF,uV} F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
        ∑ k ∈ Finset.range (m + 1), ((-1 : ℤ) ^ (n - (k + 1))) •
          FiniteLengthGrothendieckGroup.ofObject (finiteDegree.{uF,uV} F T A hA k) := by
  let := T.topology
  intro A hA hzero
  rw [alternating_degree_expansion.{uF,uV} F T (by omega)]
  symm
  apply Finset.sum_subset (Finset.range_mono hm)
  intro k _ hk
  have hmk : m < k := by
    have : ¬k < m + 1 := by simpa only [Finset.mem_range] using hk
    omega
  let : Subsingleton ((finiteDegree.{uF,uV} F T A hA k).val) := hzero k hmk
  rw [FiniteProduct.class_eq_zero, smul_zero]

/-- The fixed terminal sign turns the actual Aubert class into the class of
the actual terminal quotient, under the concrete concentration conditions. -/
theorem signed_alternating_terminal_class (m : ℕ) (hm : m + 1 ≤ n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.HasFiniteLength),
      ConcentratedAt F T A m →
      ((-1 : ℤ) ^ (n - (m + 1))) •
          alternatingOperator.{uF,uV} F T n
            (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
        FiniteLengthGrothendieckGroup.ofObject (terminalObject.{uF,uV} F T A hA m) := by
  let := T.topology
  intro A hA hcon
  rw [alternating_truncated_expansion.{uF,uV} F T m hm A hA hcon.2.2]
  exact FiniteExactEuler.signed_descending_class
    (finiteDegree.{uF,uV} F T A hA) (finiteDifferential.{uF,uV} F T A hA)
    m n hm hcon.1 hcon.2.1

/-- Actual concentration supplies common-sign effectivity without requiring
irreducibility or nonvanishing of the surviving quotient. -/
theorem effective_of_concentration (m : ℕ) (hm : m + 1 ≤ n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.HasFiniteLength),
      ConcentratedAt F T A m →
      IrreducibleGrothendieckProof.factorMap
        (((-1 : ℤ) ^ (n - (m + 1))) •
          alternatingOperator.{uF,uV} F T n
            (GeneralLinear.finiteLengthClass n F.Carrier A hA)) ∈
        VirtualRepresentation.effective := by
  let := T.topology
  intro A hA hcon
  rw [signed_alternating_terminal_class.{uF,uV} F T m hm A hA hcon]
  exact FiniteExactEuler.factorMap_ofObject_effective _

/-- At rank zero the prescribed support sign is one and the actual Aubert
operator is the identity, so every finite-length input has effective image. -/
theorem effective_rankZero (B : BlockShape 0) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear 0 F.Carrier))
      (hA : A.HasFiniteLength),
      IrreducibleGrothendieckProof.factorMap
        (((-1 : ℤ) ^ (0 - B.length)) •
          alternatingOperator.{uF,uV} F T 0
            (GeneralLinear.finiteLengthClass 0 F.Carrier A hA)) ∈
        VirtualRepresentation.effective := by
  let := T.topology
  intro A hA
  rw [alternatingOperator_rankZero]
  simp only [Nat.zero_sub, pow_zero, one_smul, LinearMap.id_apply]
  exact FiniteExactEuler.factorMap_ofObject_effective.{0,uF,max uF uV}
    (⟨A, hA⟩ : FiniteLengthObject.{0,uF,max uF uV} ℂ (GeneralLinear 0 F.Carrier))

end Langlands.Aubert.ActualCutComplex
