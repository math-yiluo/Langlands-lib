import Langlands.GroupScheme.MatrixRepresentation.AdditiveDividedPowers
import Mathlib.Data.Nat.Choose.Lucas

/-! # Characteristic-p operators of actual additive-group representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveRestrictedOperators

open AdditiveDividedPowers VectorGroupPolynomial

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The coefficient operator at a power of the characteristic. -/
def pPowerOperator (r : ℕ) : Module.End k (n → k) :=
  dividedPower ρ (p ^ r)

/-- Lucas's congruence becomes equality after casting to the coefficient field. -/
theorem choose_pow_mul_cast (r a b : ℕ) :
    (Nat.choose (p ^ r * a) (p ^ r * b) : k) = (Nat.choose a b : k) :=
  (CharP.cast_eq_iff_mod_eq k p).mpr
    Choose.choose_pow_mul_pow_mul_modEq_choose_nat

/-- Reindexing by a power of the characteristic preserves the divided-power law. -/
theorem dividedPower_pow_mul_mul (r a b : ℕ) :
    dividedPower ρ (p ^ r * a) * dividedPower ρ (p ^ r * b) =
      (Nat.choose (a + b) a : k) • dividedPower ρ (p ^ r * (a + b)) := by
  rw [dividedPower_mul, ← Nat.mul_add, choose_pow_mul_cast (k := k) p]

/-- Powers of each p-power coefficient satisfy the factorial formula. -/
theorem pPowerOperator_pow (r m : ℕ) :
    pPowerOperator ρ p r ^ m = (m.factorial : k) • dividedPower ρ (p ^ r * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hmul := dividedPower_pow_mul_mul ρ p r 1 m
    simp only [Nat.mul_one] at hmul
    rw [pow_succ', ih, mul_smul_comm, pPowerOperator, hmul, smul_smul,
      Nat.add_comm 1 m, Nat.choose_one_right, Nat.factorial_succ]
    congr 1
    push_cast
    ring

/-- Every p-power coefficient is p-nilpotent. -/
theorem pPowerOperator_pow_char (r : ℕ) : pPowerOperator ρ p r ^ p = 0 := by
  rw [pPowerOperator_pow]
  have h : (p.factorial : k) = 0 :=
    (CharP.cast_eq_zero_iff k p _).mpr
      (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)
  rw [h, zero_smul]

omit [Fact p.Prime] [CharP k p] in
/-- The p-power operators commute. -/
theorem pPowerOperator_commute (r s : ℕ) :
    pPowerOperator ρ p r * pPowerOperator ρ p s =
      pPowerOperator ρ p s * pPowerOperator ρ p r :=
  dividedPower_commute ρ _ _

omit [CharP k p] in
/-- Only finitely many p-power operators can be nonzero. -/
theorem pPowerOperator_eventually_zero :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → pPowerOperator ρ p r = 0 := by
  obtain ⟨N, hN⟩ := dividedPower_eventually_zero ρ
  refine ⟨N, fun r hr => hN _ (hr.trans ?_)⟩
  exact (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le

/-- A subalgebra containing the p-power operators contains every coefficient operator. -/
theorem dividedPower_mem_of_pPowerOperator_mem
    (A : Subalgebra k (Module.End k (n → k)))
    (hA : ∀ r, pPowerOperator ρ p r ∈ A) (m : ℕ) :
    dividedPower ρ m ∈ A := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · subst m
      rw [dividedPower_zero]
      exact A.one_mem
    by_cases hp : ∃ r, m = p ^ r
    · obtain ⟨r, rfl⟩ := hp
      exact hA r
    have hc : ∃ a ∈ Finset.Icc 1 (m - 1), (Nat.choose m a : k) ≠ 0 := by
      by_contra! hc
      apply hp
      refine ⟨multiplicity p m, ?_⟩
      apply Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat (Nat.pos_of_ne_zero hm)
      intro a ha
      exact (CharP.cast_eq_iff_mod_eq k p).mp (by simpa using hc a ha)
    obtain ⟨a, ha, hc⟩ := hc
    have ha' := Finset.mem_Icc.mp ha
    have ham : a < m := by omega
    have hma : m - a < m := by omega
    have hsum : a + (m - a) = m := Nat.add_sub_of_le ham.le
    have hprod := A.mul_mem (ih a ham) (ih (m - a) hma)
    rw [dividedPower_mul, hsum] at hprod
    have hscaled := A.smul_mem hprod ((Nat.choose m a : k)⁻¹)
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hscaled

/-- The p-power operators generate exactly the algebra of all coefficient operators. -/
theorem adjoin_range_pPowerOperator_eq_adjoin_range_dividedPower :
    Algebra.adjoin k (Set.range (pPowerOperator ρ p)) =
      Algebra.adjoin k (Set.range (dividedPower ρ)) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨r, rfl⟩
    exact Algebra.subset_adjoin ⟨p ^ r, rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨m, rfl⟩
    exact dividedPower_mem_of_pPowerOperator_mem ρ p
      (Algebra.adjoin k (Set.range (pPowerOperator ρ p)))
      (fun r => Algebra.subset_adjoin ⟨r, rfl⟩) m

/-- A subspace is invariant under all coefficients exactly when it is invariant under the
p-power coefficients. -/
theorem invariant_dividedPower_iff_invariant_pPowerOperator
    (S : Submodule k (n → k)) :
    (∀ m, ∀ v ∈ S, dividedPower ρ m v ∈ S) ↔
      ∀ r, ∀ v ∈ S, pPowerOperator ρ p r v ∈ S := by
  constructor
  · intro h r
    exact h (p ^ r)
  · intro h
    let A : Subalgebra k (Module.End k (n → k)) :=
      { carrier := {f | ∀ v ∈ S, f v ∈ S}
        algebraMap_mem' := by
          intro c v hv
          exact S.smul_mem c hv
        add_mem' := by
          intro f g hf hg v hv
          exact S.add_mem (hf v hv) (hg v hv)
        mul_mem' := by
          intro f g hf hg v hv
          exact hf _ (hg v hv) }
    intro m v hv
    exact dividedPower_mem_of_pPowerOperator_mem ρ p A h m v hv

omit [Fact p.Prime] [CharP k p] in
/-- For the one-dimensional vector group, degree indices exhaust all multi-indices. -/
theorem range_dividedPower_eq_range_coefficientOperators :
    Set.range (dividedPower ρ) = Set.range (coefficientOperators ρ) := by
  ext f
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨Finsupp.single (0 : Fin 1) m, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a 0, ?_⟩
    change coefficientOperators ρ (Finsupp.single (0 : Fin 1) (a 0)) =
      coefficientOperators ρ a
    congr 1
    exact (Finsupp.unique_single a).symm

/-- Over an infinite field, the p-power coefficients generate the algebra of all actual
affine base-field point actions. -/
theorem adjoin_range_pointOperator_eq_adjoin_range_pPowerOperator [Infinite k] :
    Algebra.adjoin k (Set.range (pointOperator ρ)) =
      Algebra.adjoin k (Set.range (pPowerOperator ρ p)) := by
  rw [adjoin_range_pointOperator_eq_adjoin_range_coefficients,
    adjoin_range_pPowerOperator_eq_adjoin_range_dividedPower,
    range_dividedPower_eq_range_coefficientOperators]

/-- Over an infinite field, the actual affine base-field point actions and the p-power
coefficients preserve the same subspaces. -/
theorem invariant_affinePoints_iff_invariant_pPowerOperator [Infinite k]
    (S : Submodule k (n → k)) :
    (∀ x, ∀ v ∈ S, pointOperator ρ x v ∈ S) ↔
      ∀ r, ∀ v ∈ S, pPowerOperator ρ p r v ∈ S := by
  rw [invariant_affinePoints_iff_invariant_coefficients]
  constructor
  · intro h r
    exact h (Finsupp.single (0 : Fin 1) (p ^ r))
  · intro h a
    have hm := (invariant_dividedPower_iff_invariant_pPowerOperator ρ p S).mpr h (a 0)
    change ∀ v ∈ S, coefficientOperators ρ (Finsupp.single (0 : Fin 1) (a 0)) v ∈ S at hm
    have ha : a = Finsupp.single (0 : Fin 1) (a 0) := Finsupp.unique_single a
    rwa [← ha] at hm

end Langlands.GroupScheme.MatrixRepresentation.AdditiveRestrictedOperators
