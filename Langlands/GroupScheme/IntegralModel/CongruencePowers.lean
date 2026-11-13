import Langlands.GroupScheme.IntegralModel.CongruenceTower
import Langlands.GroupScheme.InfinitesimalPowers

/-! # Powers in the actual integral-model congruence tower -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

section Coefficients

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The actual congruence coefficient transition as an algebra map over the
original integral base. -/
def congruenceTransitionAlgHom {n k : ℕ+} (h : n ≤ k) :
    congruenceRing R k →ₐ[CommRingCat.of R] congruenceRing R n :=
  Ideal.Quotient.factorₐ (CommRingCat.of R)
    (Ideal.pow_le_pow_right (show (n : ℕ) ≤ (k : ℕ) from h))

@[simp] theorem congruenceTransitionAlgHom_apply {n k : ℕ+} (h : n ≤ k)
    (x : congruenceRing R k) :
    congruenceTransitionAlgHom R h x = congruenceRingTransition R h x := rfl

/-- Between levels at most twice as deep, the coefficient transition has
square-zero kernel. -/
theorem congruenceTransitionAlgHom_ker_sq {n k : ℕ+} (h : n ≤ k)
    (hk : (k : ℕ) ≤ (n : ℕ) + (n : ℕ)) :
    (RingHom.ker (congruenceTransitionAlgHom R h)) ^ 2 = ⊥ := by
  apply le_antisymm ?_ bot_le
  rw [pow_two, Ideal.mul_le]
  intro a ha b hb
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ha' : a ∈ (IsLocalRing.maximalIdeal R) ^ (n : ℕ) :=
    Ideal.Quotient.eq_zero_iff_mem.mp ha
  have hb' : b ∈ (IsLocalRing.maximalIdeal R) ^ (n : ℕ) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hb
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.pow_le_pow_right hk
  rw [pow_add]
  exact Ideal.mul_mem_mul ha' hb'

/-- A natural number in the maximal ideal annihilates the coefficient kernel
of every adjacent positive congruence transition. -/
theorem congruenceTransitionAlgHom_ker_annihilated (n : ℕ+) (p : ℕ)
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (a : congruenceRing R (n + 1))
    (ha : a ∈ RingHom.ker
      (congruenceTransitionAlgHom R (le_of_lt (PNat.lt_add_right n 1)))) :
    (p : congruenceRing R (n + 1)) * a = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have ha' : a ∈ (IsLocalRing.maximalIdeal R) ^ (n : ℕ) :=
    Ideal.Quotient.eq_zero_iff_mem.mp ha
  rw [← map_natCast (Ideal.Quotient.mk _) p, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  change (p : R) * a ∈ (IsLocalRing.maximalIdeal R) ^ ((n : ℕ) + 1)
  rw [pow_succ']
  exact Ideal.mul_mem_mul hp ha'

end Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

/-- Points of the actual congruence fibre are coefficient points of the
original model, with their original group law. -/
def congruenceAffinePointsEquiv (n : ℕ+) :
    rationalPoints (M.congruenceFibre n) ≃*
      Lie.AffinePoints M.group (congruenceRing R n) :=
  baseChangeBasePointsEquiv (congruenceBaseMap R n) M.group

/-- The actual fibre transition is precisely extension of coefficients for the
original model. -/
theorem congruenceAffinePointsEquiv_transition {n k : ℕ+} (h : n ≤ k)
    (x : rationalPoints (M.congruenceFibre k)) :
    M.congruenceAffinePointsEquiv n (M.congruenceTransition h x) =
      Lie.affineMap M.group (congruenceTransitionAlgHom R h)
        (M.congruenceAffinePointsEquiv k x) :=
  baseChangePointRestriction_project _ _ _ _ _ _

/-- A natural number lying in the maximal ideal moves every original
integral section one step deeper in the positive congruence tower. -/
theorem pow_mem_congruenceKernelAt_succ (n : ℕ+) (p : ℕ)
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {x : M.integralSections} (hx : x ∈ M.congruenceKernelAt n) :
    x ^ p ∈ M.congruenceKernelAt (n + 1) := by
  let h : n ≤ n + 1 := le_of_lt (PNat.lt_add_right n 1)
  have hx' :
      Lie.affineMap M.group (congruenceTransitionAlgHom R h)
        (M.congruenceAffinePointsEquiv (n + 1) (M.reductionAt (n + 1) x)) = 1 := by
    rw [← M.congruenceAffinePointsEquiv_transition,
      M.congruenceTransition_reductionAt, hx, map_one]
  have hsq := congruenceTransitionAlgHom_ker_sq R h
    (by have := n.pos; change (n : ℕ) + 1 ≤ (n : ℕ) + (n : ℕ); omega)
  have hpw := Lie.affineKernel_pow_eq_one M.group
    (congruenceTransitionAlgHom R h) hsq p
    (congruenceTransitionAlgHom_ker_annihilated R n p hp) _ hx'
  rw [mem_congruenceKernelAt]
  apply (M.congruenceAffinePointsEquiv (n + 1)).injective
  simpa only [map_pow, map_one] using hpw

/-- The power step holds for the same congruence subgroups inside the given
generic rational-point group. -/
theorem pow_mem_congruenceSubgroupAt_succ (n : ℕ+) (p : ℕ)
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {x : rationalPoints G} (hx : x ∈ M.congruenceSubgroupAt n) :
    x ^ p ∈ M.congruenceSubgroupAt (n + 1) := by
  obtain ⟨x, hx, rfl⟩ := hx
  exact ⟨x ^ p, M.pow_mem_congruenceKernelAt_succ n p hp hx, map_pow _ _ _⟩

/-- Iterating the power step moves an original integral section arbitrarily
deep in the actual congruence tower. -/
theorem pow_pow_mem_congruenceKernelAt (n : ℕ+) (p : ℕ)
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {x : M.integralSections} (hx : x ∈ M.congruenceKernelAt n) (m : ℕ) :
    x ^ (p ^ m) ∈ M.congruenceKernelAt
      ⟨(n : ℕ) + m, Nat.add_pos_left n.pos m⟩ := by
  induction m with
  | zero =>
    have hn : (⟨(n : ℕ) + 0, Nat.add_pos_left n.pos 0⟩ : ℕ+) = n := by
      apply Subtype.ext
      rfl
    simpa only [hn, pow_zero, pow_one] using hx
  | succ m ih =>
    have h := M.pow_mem_congruenceKernelAt_succ
      ⟨(n : ℕ) + m, Nat.add_pos_left n.pos m⟩ p hp ih
    have hn : (⟨(n : ℕ) + m, Nat.add_pos_left n.pos m⟩ : ℕ+) + 1 =
        ⟨(n : ℕ) + (m + 1), Nat.add_pos_left n.pos (m + 1)⟩ := by
      apply Subtype.ext
      change (n : ℕ) + m + 1 = (n : ℕ) + (m + 1)
      omega
    rw [hn] at h
    rw [pow_succ, pow_mul]
    exact h

/-- Iterated powers in the original generic rational points satisfy the same
actual congruence bounds. -/
theorem pow_pow_mem_congruenceSubgroupAt (n : ℕ+) (p : ℕ)
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    {x : rationalPoints G} (hx : x ∈ M.congruenceSubgroupAt n) (m : ℕ) :
    x ^ (p ^ m) ∈ M.congruenceSubgroupAt
      ⟨(n : ℕ) + m, Nat.add_pos_left n.pos m⟩ := by
  obtain ⟨x, hx, rfl⟩ := hx
  exact ⟨x ^ (p ^ m), M.pow_pow_mem_congruenceKernelAt n p hp hx m, map_pow _ _ _⟩

omit [IsDomain R] in
/-- The actual residue characteristic lies in the original maximal ideal. -/
theorem residueChar_mem_maximalIdeal :
    (ringChar (IsLocalRing.ResidueField R) : R) ∈ IsLocalRing.maximalIdeal R := by
  apply (IsLocalRing.residue_eq_zero_iff _).mp
  simp

end Langlands.GroupScheme.IntegralModel
