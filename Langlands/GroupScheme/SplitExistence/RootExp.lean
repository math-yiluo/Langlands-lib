import Langlands.GroupScheme.SplitExistence.ChevalleyData

/-! # The exponential of a divided-power family

For a family `e : ℕ → Matrix (Fin n) (Fin n) ℤ` with `e 0 = 1`,
`e a * e c = C(a+c, a) • e (a+c)` and `e k = 0` for `k > n`, the truncated exponential
`divExp e` is a homomorphism from the additive group of any commutative ring to the units of
matrices. -/

noncomputable section

open Matrix Finset

namespace Langlands.GroupScheme.SplitExistence

variable {n : ℕ} {e : ℕ → Matrix (Fin n) (Fin n) ℤ}

/-- The axioms of a divided-power family of integral `n × n` matrices. -/
structure IsDividedPowerFamily (e : ℕ → Matrix (Fin n) (Fin n) ℤ) : Prop where
  zero : e 0 = 1
  mul : ∀ a c, e a * e c = ((a + c).choose a : ℤ) • e (a + c)
  eq_zero : ∀ k, n < k → e k = 0

variable {R : Type*} [CommRing R]

theorem divExp_zero (he : IsDividedPowerFamily e) : divExp e (0 : R) = 1 := by
  rw [divExp, Finset.sum_eq_single 0]
  · simp [he.zero]
  · intro k _ hk
    simp [zero_pow hk]
  · simp

/-- The truncated exponential is additive: `exp(s) exp(t) = exp(s + t)`. -/
theorem divExp_mul (he : IsDividedPowerFamily e) (s t : R) :
    divExp e s * divExp e t = divExp e (s + t) := by
  set E : ℕ → Matrix (Fin n) (Fin n) R := fun k => (e k).map (Int.castRingHom R) with hE
  have hEmul : ∀ a c, E a * E c = ((a + c).choose a : R) • E (a + c) := by
    intro a c
    ext i j
    have h := congrArg (fun M => M i j) (he.mul a c)
    simp only [Matrix.smul_apply, smul_eq_mul] at h
    simp only [hE, ← Matrix.map_mul, Matrix.map_apply, h, Matrix.smul_apply, smul_eq_mul,
      eq_intCast, Int.cast_mul, Int.cast_natCast]
  have hEzero : ∀ k, n < k → E k = 0 := by
    intro k hk
    simp [hE, he.eq_zero k hk]
  let f : ℕ × ℕ → Matrix (Fin n) (Fin n) R := fun p =>
    (s ^ p.1 * t ^ p.2 * ((p.1 + p.2).choose p.1 : R)) • E (p.1 + p.2)
  have hL : divExp e s * divExp e t = ∑ p ∈ range (n + 1) ×ˢ range (n + 1), f p := by
    rw [divExp, divExp, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    change (s ^ a • E a) * (t ^ c • E c) = f (a, c)
    rw [smul_mul_smul_comm, hEmul]
    simp only [f, smul_smul]
  have hR : divExp e (s + t) =
      ∑ m ∈ range (n + 1), ∑ p ∈ antidiagonal m, f p := by
    rw [divExp]
    refine Finset.sum_congr rfl fun m _ => ?_
    change (s + t) ^ m • E m = _
    rw [add_pow, Finset.sum_smul, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a c => (s ^ a * t ^ c * (m.choose a : R)) • E m)]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    simp only [f, hp]
  rw [hL, hR, Finset.sum_sigma']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.2) ?_ ?_ ?_ ?_
  · rintro ⟨m, a, c⟩ hx _
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hx
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  · rintro ⟨m, a, c⟩ hx _ ⟨m', a', c'⟩ hx' _ h
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx hx'
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : m = m' := by omega
    subst this
    rfl
  · rintro ⟨a, c⟩ hp hf
    refine ⟨⟨a + c, a, c⟩, ?_, ?_, rfl⟩
    · simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal, and_true]
      by_contra h
      apply hf
      simp only [f, hEzero (a + c) (by omega), smul_zero]
    · simpa using hf
  · rintro ⟨m, a, c⟩ _ _
    rfl

/-- The truncated exponential as a unit, `exp(-s)` being its inverse. -/
def divExpUnit (he : IsDividedPowerFamily e) (s : R) : GL (Fin n) R where
  val := divExp e s
  inv := divExp e (-s)
  val_inv := by rw [divExp_mul he, add_neg_cancel, divExp_zero he]
  inv_val := by rw [divExp_mul he, neg_add_cancel, divExp_zero he]

@[simp]
theorem coe_divExpUnit (he : IsDividedPowerFamily e) (s : R) :
    (divExpUnit he s : Matrix (Fin n) (Fin n) R) = divExp e s :=
  rfl

/-- The truncated exponential as a homomorphism `(R, +) → GL_n(R)`. -/
def divExpHom (he : IsDividedPowerFamily e) : Multiplicative R →* GL (Fin n) R where
  toFun s := divExpUnit he s.toAdd
  map_one' := Units.ext (divExp_zero he)
  map_mul' s t := Units.ext (divExp_mul he s.toAdd t.toAdd).symm

theorem divExp_map {S : Type*} [CommRing S] (f : R →+* S) (s : R) :
    (divExp e s).map f = divExp e (f s) := by
  change f.mapMatrix (divExp e s) = _
  rw [divExp, divExp, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]

end Langlands.GroupScheme.SplitExistence
