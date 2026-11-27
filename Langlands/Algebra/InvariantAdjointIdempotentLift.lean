import Langlands.Algebra.ComplementaryAdjointIdempotentLift
import Langlands.Algebra.RegularTraceIntertwinerAverage
import Mathlib.Algebra.Star.Subalgebra

/-! # Lifting an invariant Lagrangian projection in the endomorphism algebra -/

namespace Langlands.Algebra

open scoped BigOperators

private theorem half_smul_double {S : Type*} [Ring S] [Algebra ℚ S] (x : S) :
    (1 / 2 : ℚ) • (x + x) = x := by
  rw [← two_smul ℚ, smul_smul]
  norm_num

/-- A projection onto an invariant Lagrangian can be replaced by one with
the same image which commutes with the action and whose adjoint is its complement. -/
theorem exists_commuting_complementary_projection
    {A S : Type*} [Ring A] [StarRing A] [Algebra ℚ A]
    [FiniteDimensional ℚ A] [IsSimpleRing A] [Ring S] [StarRing S] [Algebra ℚ S]
    (ρ : A →ₐ[ℚ] S) (hρ : ∀ a, ρ (star a) = star (ρ a))
    (p : S) (his : star p * p = 0) (hco : p * (1 - star p) = 1 - star p)
    (hstable : ∀ a, p * (ρ a * p) = ρ a * p) :
    ∃ e : S, IsIdempotentElem e ∧ p * e = e ∧ e * p = p ∧ star e = 1 - e ∧
      ∀ a, ρ a * e = e * ρ a := by
  classical
  let b := Module.finBasis ℚ A
  let q := regularTraceAverage b ρ ρ p
  obtain ⟨hpq, hqp⟩ := regularTraceAverage_same_image b ρ p hstable
  change p * q = q at hpq
  change q * p = p at hqp
  have hqid : q * q = q := by
    calc
      q * q = q * (p * q) := by rw [hpq]
      _ = (q * p) * q := (mul_assoc ..).symm
      _ = q := by rw [hqp, hpq]
  have ha : star q * star p = star q := by
    simpa only [star_mul] using congrArg star hpq
  have hb : star p * star q = star p := by
    simpa only [star_mul] using congrArg star hqp
  have hqIs : star q * q = 0 := by
    calc
      star q * q = (star q * star p) * (p * q) := by rw [ha, hpq]
      _ = (star q * (star p * p)) * q := by simp only [mul_assoc]
      _ = 0 := by rw [his, mul_zero, zero_mul]
  have ht : (1 - star p) * (1 - star q) = 1 - star q := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hb, sub_self, sub_zero]
  have hqt : q * (1 - star q) = 1 - star q := by
    calc
      _ = q * ((1 - star p) * (1 - star q)) := by rw [ht]
      _ = (q * (1 - star p)) * (1 - star q) := (mul_assoc ..).symm
      _ = (q * (p * (1 - star p))) * (1 - star q) := by rw [hco]
      _ = 1 - star q := by rw [← mul_assoc q, hqp, hco, ht]
  have htq : (1 - star q) * q = q := by rw [sub_mul, one_mul, hqIs, sub_zero]
  let e : S := (1 / 2 : ℚ) • (q + (1 - star q))
  have hqe : q * e = e := by simp only [e, mul_smul_comm, mul_add, hqid, hqt]
  have heq : e * q = q := by
    simp only [e, smul_mul_assoc, add_mul, hqid, htq, half_smul_double]
  have heStar : star e = 1 - e := by
    apply eq_sub_of_add_eq
    simp only [e, star_rat_smul, star_add, star_sub, star_one, star_star, ← smul_add]
    have hsum : (star q + (1 - q)) + (q + (1 - star q)) = 1 + 1 := by abel
    rw [hsum, half_smul_double]
  have hqComm (a : A) : ρ a * q = q * ρ a := regularTraceAverage_intertwines b ρ ρ p a
  have hsComm (a : A) : ρ a * star q = star q * ρ a := by
    simpa only [star_mul, hρ, star_star] using (congrArg star (hqComm (star a))).symm
  refine ⟨e, ?_, ?_, ?_, heStar, ?_⟩
  · change e * e = e
    calc
      e * e = e * (q * e) := congrArg (e * ·) hqe.symm
      _ = (e * q) * e := (mul_assoc ..).symm
      _ = e := by rw [heq, hqe]
  · calc
      p * e = p * (q * e) := by rw [hqe]
      _ = e := by rw [← mul_assoc, hpq, hqe]
  · calc
      e * p = e * (q * p) := by rw [hqp]
      _ = p := by rw [← mul_assoc, heq, hqp]
  · intro a
    simp only [e, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul,
      mul_one, one_mul, hqComm, hsComm]

/-- A complementary adjoint idempotent commuting with a simple rational
algebra action lifts to one commuting with the original action. -/
theorem exists_lift_commuting_idempotent_star_eq_one_sub
    {A R S : Type*} [Ring A] [StarRing A] [Algebra ℚ A]
    [FiniteDimensional ℚ A] [IsSimpleRing A]
    [Ring R] [StarRing R] [Algebra ℚ R] [Ring S] [StarRing S] [Algebra ℚ S]
    (ρ : A →ₐ[ℚ] R) (hρ : ∀ a, ρ (star a) = star (ρ a))
    (f : R →ₐ[ℚ] S) (hf : Function.Surjective f) (hstar : ∀ x, f (star x) = star (f x))
    (hker : ∀ x, f x = 0 → x ^ 2 = 0)
    (e : S) (he : IsIdempotentElem e) (heStar : star e = 1 - e)
    (heComm : ∀ a, f (ρ a) * e = e * f (ρ a)) :
    ∃ p : R, IsIdempotentElem p ∧ f p = e ∧ star p = 1 - p ∧
      ∀ a, ρ a * p = p * ρ a := by
  let C := StarSubalgebra.centralizer ℚ (Set.range ρ)
  let D := StarSubalgebra.centralizer ℚ (Set.range (f.comp ρ))
  have hC {x : R} : x ∈ C ↔ ∀ a, ρ a * x = x * ρ a := by
    rw [StarSubalgebra.mem_centralizer_iff]
    constructor
    · exact fun h a => (h _ ⟨a, rfl⟩).1
    · rintro h _ ⟨a, rfl⟩
      exact ⟨h a, hρ a ▸ h (star a)⟩
  have hD {x : S} : x ∈ D ↔ ∀ a, f (ρ a) * x = x * f (ρ a) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    constructor
    · exact fun h a => (h _ ⟨a, rfl⟩).1
    · rintro h _ ⟨a, rfl⟩
      change f (ρ a) * x = x * f (ρ a) ∧ star (f (ρ a)) * x = x * star (f (ρ a))
      exact ⟨h a, by rw [← hstar, ← hρ]; exact h (star a)⟩
  let g : C →ₐ[ℚ] D :=
    (f.comp C.subtype.toAlgHom).codRestrict D.toSubalgebra (fun x => hD.mpr (fun a => by
      change f (ρ a) * f (x : R) = f (x : R) * f (ρ a)
      rw [← map_mul, ← map_mul, hC.mp x.property a]))
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hxy, hx⟩ := exists_commuting_lift_of_surjective ρ f hf y (hD.mp y.property)
    exact ⟨⟨x, hC.mpr hx⟩, Subtype.ext hxy⟩
  let e' : D := ⟨e, hD.mpr heComm⟩
  obtain ⟨p, hp, hpe, hpstar⟩ := exists_lift_idempotent_star_eq_one_sub g hg
    (fun x => Subtype.ext (hstar x))
    (fun x hx => Subtype.ext (hker x (congrArg Subtype.val hx)))
    e' (Subtype.ext he) (Subtype.ext heStar)
  exact ⟨p, congrArg Subtype.val hp, congrArg Subtype.val hpe,
    congrArg Subtype.val hpstar, hC.mp p.property⟩

end Langlands.Algebra
