import Langlands.GroupScheme.Rational.LaurentAugmentation
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.Int.Basic

/-! # Frobenius orbits of nonzero Laurent characters -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.LaurentAugmentation

/-- A nonzero character that is not divisible by `p`. -/
def IsPrimitive (p : ℕ) {M : Type v} [AddCommMonoid M] (m : M) : Prop :=
  m ≠ 0 ∧ ¬ ∃ n : M, p • n = m

section Orbits

variable {p : ℕ} [hp : Fact p.Prime]
variable {M : Type v} [AddCommMonoid M] [IsAddTorsionFree M]

theorem primitive_pow_smul_injective :
    Function.Injective (fun x : {m : M // IsPrimitive p m} × ℕ =>
      (p ^ x.2) • x.1.val) := by
  rintro ⟨a, r⟩ ⟨b, s⟩ h
  suffices r = s ∧ a = b by
    rcases this with ⟨rfl, rfl⟩
    rfl
  have hle : ∀ (a b : {m : M // IsPrimitive p m}) (r s : ℕ),
      r ≤ s → p ^ r • a.val = p ^ s • b.val → r = s ∧ a = b := by
    intro a b r s hrs h
    have heq : a.val = p ^ (s - r) • b.val := by
      apply nsmul_right_injective (n := p ^ r) (pow_ne_zero _ hp.out.ne_zero)
      change p ^ r • a.val = p ^ r • (p ^ (s - r) • b.val)
      rw [← mul_nsmul', ← pow_add, Nat.add_sub_cancel' hrs]
      exact h
    have hrs' : r = s := by
      by_contra hne
      have hpos : 0 < s - r := by omega
      obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s - r ≠ 0)
      apply a.property.2
      refine ⟨p ^ t • b.val, ?_⟩
      rw [heq, ht, pow_succ', mul_nsmul']
    refine ⟨hrs', Subtype.ext ?_⟩
    simpa [hrs'] using heq
  rcases le_total r s with hrs | hsr
  · exact hle a b r s hrs h
  · obtain ⟨hrs, hab⟩ := hle b a s r hsr h.symm
    exact ⟨hrs.symm, hab.symm⟩

variable (p) (I : Type v)

theorem exists_primitive_pow_smul {m : I → ℤ} (hm : m ≠ 0) :
    ∃ (a : I → ℤ) (r : ℕ), IsPrimitive p a ∧ p ^ r • a = m := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hm
  suffices ∀ d : ℕ, ∀ m : I → ℤ, (m i).natAbs = d → m i ≠ 0 →
      ∃ (a : I → ℤ) (r : ℕ), IsPrimitive p a ∧ p ^ r • a = m from
    this _ m rfl hi
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro m hd hmi
    by_cases hdiv : ∃ n : I → ℤ, p • n = m
    · obtain ⟨n, hn⟩ := hdiv
      have hni : n i ≠ 0 := by
        intro hz
        apply hmi
        rw [← hn, Pi.smul_apply, hz, smul_zero]
      have habs : d = p * (n i).natAbs := by
        rw [← hd, ← hn, Pi.smul_apply, nsmul_eq_mul, Int.natAbs_mul]
        simp
      have hlt : (n i).natAbs < d := by
        have hpos : 0 < (n i).natAbs := Int.natAbs_pos.mpr hni
        have hp1 := hp.out.one_lt
        rw [habs]
        nlinarith
      obtain ⟨a, r, ha, har⟩ := ih _ hlt n rfl hni
      refine ⟨a, r + 1, ha, ?_⟩
      rw [pow_succ', mul_nsmul', har, hn]
    · exact ⟨m, 0, ⟨fun hz => hmi (congrFun hz i), hdiv⟩, by simp⟩

/-- Nonzero integer characters are uniquely primitive characters times a power of `p`. -/
def orbitEquiv : ({m : I → ℤ // IsPrimitive p m} × ℕ) ≃ {m : I → ℤ // m ≠ 0} :=
  Equiv.ofBijective
    (fun x => ⟨p ^ x.2 • x.1.val, fun hz => x.1.property.1
      ((nsmul_eq_zero_iff_right (pow_ne_zero _ hp.out.ne_zero)).mp hz)⟩)
    ⟨fun _ _ h => primitive_pow_smul_injective (congrArg Subtype.val h), by
      rintro ⟨m, hm⟩
      obtain ⟨a, r, ha, har⟩ := exists_primitive_pow_smul p I hm
      exact ⟨(⟨a, ha⟩, r), Subtype.ext har⟩⟩

@[simp] theorem orbitEquiv_apply (a : {m : I → ℤ // IsPrimitive p m}) (r : ℕ) :
    (orbitEquiv p I (a, r)).val = p ^ r • a.val := rfl

end Orbits

section Basis

variable (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
variable (I : Type v)

/-- A basis of the pointed Laurent functions consisting of iterated Frobenius powers
of the pointed monomials indexed by primitive nonzero characters. -/
def frobeniusBasis :
    Module.Basis ({m : I → ℤ // IsPrimitive p m} × ℕ) k (space k (I → ℤ)) :=
  (basis (k := k) (M := I → ℤ)).reindex (orbitEquiv p I).symm

@[simp] theorem frobeniusBasis_apply (a : {m : I → ℤ // IsPrimitive p m}) (r : ℕ) :
    ((frobeniusBasis k p I) (a, r)).val = delta k (I → ℤ) a.val ^ p ^ r := by
  rw [frobeniusBasis, Module.Basis.reindex_apply, basis_apply, delta_pow]
  rfl

end Basis

end Langlands.GroupScheme.LaurentAugmentation
