/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic

/-!
# Invariant compatible characters of `ℓ`-power torsion

Let `A` be an `ℓ`-divisible abelian group with finite `ℓ ^ n`-torsion `A[ℓ ^ n]`, and let `σ` be
an endomorphism of `A` with finitely many fixed points, for instance the Frobenius acting on the
geometric points of an abelian variety over a finite field. A *compatible system of
characters* is a family of homomorphisms `ψ n : A[ℓ ^ n] → ℤ / ℓ ^ n` with
`ψ n (ℓ • y) = ψ (n + 1) y mod ℓ ^ n`, i.e. an element of
`lim_n Hom(A[ℓ ^ n], ℤ / ℓ ^ n) = Hom(T_ℓ A, ℤ_ℓ)`. If every `ψ n` is invariant
under `σ`, then all `ψ n` vanish (`AddSubgroup.eq_zero_of_forall_map_eq_of_finite_fixedPoints`).

This is the dual form of the absence of `σ`-fixed vectors in the Tate module `T_ℓ A`. Instead of
the determinant argument over `ℤ_ℓ`, the proof bounds the cokernel of `σ - 1` on the finite
groups `A[ℓ ^ n]` uniformly in `n`: it has the same order as the kernel, which consists of fixed
points. Hence `ℓ ^ N` maps `A[ℓ ^ n]` into the image of `σ - 1`, on which every invariant
character vanishes, for a fixed `N`; compatibility and divisibility then kill `ψ n`.
-/

@[expose] public section

namespace AddSubgroup

variable {G : Type*} [AddCommGroup G]

/-- If an endomorphism `f` of a finite abelian group `G` killed by `ℓ ^ n` (`ℓ` prime) has at
most `N` elements in its kernel, then `ℓ ^ N` maps `G` into the range of `f`: the cokernel of `f`
has the same order as its kernel, and is an `ℓ`-group. -/
theorem pow_zsmul_mem_range_of_natCard_ker_le [Finite G] {ℓ : ℕ} (hℓ : ℓ.Prime) {n : ℕ}
    (hG : ∀ x : G, (ℓ : ℤ) ^ n • x = 0) (f : G →+ G) {N : ℕ} (hN : Nat.card f.ker ≤ N)
    (x : G) : (ℓ : ℤ) ^ N • x ∈ f.range := by
  set Q := G ⧸ f.range
  have hcard : Nat.card Q = Nat.card f.ker := by
    have h₁ := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.range
    have h₂ := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv] at h₂
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    rw [h₂, mul_comm] at h₁
    exact (Nat.eq_of_mul_eq_mul_right hpos h₁).symm
  have hQ : Nat.card Q ≤ N := hcard ▸ hN
  set y : Q := (x : Q)
  have hy : (ℓ ^ n : ℕ) • y = 0 := by
    rw [← natCast_zsmul, Nat.cast_pow, ← QuotientAddGroup.mk_zsmul, hG, QuotientAddGroup.mk_zero]
  obtain ⟨j, hj, hjy⟩ := (Nat.dvd_prime_pow hℓ).1 (addOrderOf_dvd_of_nsmul_eq_zero hy)
  have hdvd : ℓ ^ j ∣ Nat.card Q := hjy ▸ _root_.addOrderOf_dvd_natCard y
  have hle : ℓ ^ j ≤ N := (Nat.le_of_dvd Nat.card_pos hdvd).trans hQ
  have hjN : j ≤ N := (Nat.lt_pow_self hℓ.one_lt).le.trans hle
  have hyN : (ℓ ^ N : ℕ) • y = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.1 (hjy ▸ pow_dvd_pow ℓ hjN)
  rw [← natCast_zsmul, Nat.cast_pow, ← QuotientAddGroup.mk_zsmul] at hyN
  exact (QuotientAddGroup.eq_zero_iff _).1 hyN

variable {A : Type*} [AddCommGroup A] {ℓ : ℕ}

/-- An element of `ℤ / ℓ ^ (n + k)` killed by `ℓ ^ k` reduces to zero modulo `ℓ ^ n`. -/
theorem _root_.ZMod.castHom_eq_zero_of_pow_mul_eq_zero (hℓ : ℓ.Prime) {n k : ℕ}
    {a : ZMod (ℓ ^ (n + k))} (ha : ((ℓ ^ k : ℕ) : ZMod (ℓ ^ (n + k))) * a = 0) :
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n k)) (ZMod (ℓ ^ n)) a = 0 := by
  have : NeZero (ℓ ^ (n + k)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  have h' : ℓ ^ (n + k) ∣ ℓ ^ k * a.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id]
    exact ha
  have h'' : ℓ ^ k * ℓ ^ n ∣ ℓ ^ k * a.val := by rwa [← pow_add, add_comm k n]
  exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hℓ.pos k) h''

/-- Iterating the compatibility of a system `a n ∈ ℤ / ℓ ^ n` under reduction. -/
theorem _root_.ZMod.castHom_eq_of_forall_castHom_succ (a : ∀ n : ℕ, ZMod (ℓ ^ n))
    (ha : ∀ n, ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1)) (ZMod (ℓ ^ n)) (a (n + 1)) =
      a n) (n k : ℕ) :
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n k)) (ZMod (ℓ ^ n)) (a (n + k)) = a n := by
  induction k with
  | zero => rw [ZMod.castHom_apply]; exact ZMod.cast_id _ _
  | succ k ih =>
    rw [← ih, ← ha (n + k), ← RingHom.comp_apply, ZMod.castHom_comp]
    rfl

/-- Iterating the compatibility `ψ n (ℓ • y) = ψ (n + 1) y mod ℓ ^ n` of a system of characters
`ψ n : A[ℓ ^ n] → ℤ / ℓ ^ n`. -/
theorem map_pow_zsmul_eq_castHom (ψ : ∀ n : ℕ, torsionBy A ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n))
    (hψ : ∀ n (y : torsionBy A ((ℓ : ℤ) ^ (n + 1))),
      ψ n ⟨(ℓ : ℤ) • (y : A), zsmul_mem_torsionBy_pow y.2⟩ =
        ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) _ (ψ (n + 1) y))
    (n k : ℕ) (z : A) (hz : z ∈ torsionBy A ((ℓ : ℤ) ^ (n + k)))
    (hz' : (ℓ : ℤ) ^ k • z ∈ torsionBy A ((ℓ : ℤ) ^ n)) :
    ψ n ⟨(ℓ : ℤ) ^ k • z, hz'⟩ =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n k)) _ (ψ (n + k) ⟨z, hz⟩) := by
  induction k generalizing z with
  | zero =>
    have h : (⟨(ℓ : ℤ) ^ 0 • z, hz'⟩ : torsionBy A ((ℓ : ℤ) ^ n)) = ⟨z, hz⟩ :=
      Subtype.ext (by simp)
    rw [h, ZMod.castHom_apply]
    exact (ZMod.cast_id _ _).symm
  | succ k ih =>
    have hz₁ : (ℓ : ℤ) • z ∈ torsionBy A ((ℓ : ℤ) ^ (n + k)) :=
      zsmul_mem_torsionBy_pow (n := n + k) hz
    have h : (⟨(ℓ : ℤ) ^ (k + 1) • z, hz'⟩ : torsionBy A ((ℓ : ℤ) ^ n)) =
        ⟨(ℓ : ℤ) ^ k • ((ℓ : ℤ) • z), by rw [smul_smul, ← pow_succ]; exact hz'⟩ :=
      Subtype.ext (by simp [pow_succ, mul_smul])
    rw [h, ih _ hz₁, hψ (n + k) ⟨z, hz⟩, ← RingHom.comp_apply, ZMod.castHom_comp]
    rfl

/-- **Invariant compatible characters of `ℓ`-power torsion vanish.** Let `A` be an `ℓ`-divisible
abelian group whose `ℓ ^ n`-torsion is finite for every `n`, and let `σ` be an endomorphism of
`A` with finitely many fixed points. Then every compatible system of `σ`-invariant characters
`ψ n : A[ℓ ^ n] → ℤ / ℓ ^ n`, `ψ n (ℓ • y) = ψ (n + 1) y mod ℓ ^ n`, is zero.

Equivalently, `σ` has no nonzero fixed vector on `Hom(T_ℓ A, ℤ_ℓ) = lim_n Hom(A[ℓ ^ n], ℤ / ℓ ^ n)`.
-/
theorem eq_zero_of_forall_map_eq_of_finite_fixedPoints (hℓ : ℓ.Prime) (σ : A →+ A)
    (hfix : {a | σ a = a}.Finite) (hfin : ∀ n : ℕ, Finite (torsionBy A ((ℓ : ℤ) ^ n)))
    (hdiv : ∀ x : A, ∃ y, (ℓ : ℤ) • y = x)
    (ψ : ∀ n : ℕ, torsionBy A ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n))
    (hσ : ∀ n (y : torsionBy A ((ℓ : ℤ) ^ n)),
      ψ n ⟨σ y, apply_mem_torsionBy σ y.2⟩ = ψ n y)
    (hψ : ∀ n (y : torsionBy A ((ℓ : ℤ) ^ (n + 1))),
      ψ n ⟨(ℓ : ℤ) • (y : A), zsmul_mem_torsionBy_pow y.2⟩ =
        ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) _ (ψ (n + 1) y))
    (n : ℕ) : ψ n = 0 := by
  set N := Nat.card hfix.toFinset
  -- `σ - 1` on `A[ℓ ^ m]`, whose kernel consists of fixed points
  let f (m : ℕ) : torsionBy A ((ℓ : ℤ) ^ m) →+ torsionBy A ((ℓ : ℤ) ^ m) :=
    { toFun y := ⟨σ y - y, sub_mem (apply_mem_torsionBy σ y.2) y.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' y z := Subtype.ext (by simp only [AddMemClass.coe_add, map_add]; abel) }
  have hker (m : ℕ) : Nat.card (f m).ker ≤ N := by
    have hinj : Function.Injective fun y : (f m).ker ↦
        (⟨((y : torsionBy A ((ℓ : ℤ) ^ m)) : A), by
          have h := congrArg Subtype.val ((AddMonoidHom.mem_ker).1 y.2)
          simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ZeroMemClass.coe_zero] at h
          simpa [sub_eq_zero] using h⟩ : hfix.toFinset) := fun y z h ↦
      Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
    have : Finite hfix.toFinset := inferInstance
    exact Nat.card_le_card_of_injective _ hinj
  -- `ψ m` vanishes on `ℓ ^ N • A[ℓ ^ m]`
  have hkill (m : ℕ) (w : torsionBy A ((ℓ : ℤ) ^ m)) : ψ m ((ℓ : ℤ) ^ N • w) = 0 := by
    have := hfin m
    obtain ⟨v, hv⟩ := pow_zsmul_mem_range_of_natCard_ker_le hℓ
      (fun x : torsionBy A ((ℓ : ℤ) ^ m) ↦ Subtype.ext x.2) (f m) (hker m) w
    rw [← hv]
    change ψ m (⟨σ v, apply_mem_torsionBy σ v.2⟩ - v) = 0
    rw [map_sub, hσ, sub_self]
  ext ⟨y, hy⟩
  -- write `y = ℓ ^ N • z` with `z ∈ A[ℓ ^ (n + N)]`
  have hdivN : ∀ k : ℕ, ∀ x : A, ∃ z, (ℓ : ℤ) ^ k • z = x := by
    intro k
    induction k with
    | zero => exact fun x ↦ ⟨x, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨z, rfl⟩ := ih x
      obtain ⟨z', rfl⟩ := hdiv z
      exact ⟨z', by rw [pow_succ, mul_smul]⟩
  obtain ⟨z, rfl⟩ := hdivN N y
  have hz : z ∈ torsionBy A ((ℓ : ℤ) ^ (n + N)) := by
    change (ℓ : ℤ) ^ (n + N) • z = 0
    rw [pow_add, mul_smul]
    exact hy
  rw [map_pow_zsmul_eq_castHom ψ hψ n N z hz hy, AddMonoidHom.zero_apply]
  -- `ℓ ^ N • ψ (n + N) z = 0` in `ℤ / ℓ ^ (n + N)`, so `ψ (n + N) z` reduces to zero mod `ℓ ^ n`
  set a := ψ (n + N) ⟨z, hz⟩
  have ha : ((ℓ ^ N : ℕ) : ZMod (ℓ ^ (n + N))) * a = 0 := by
    have h := hkill (n + N) ⟨z, hz⟩
    rw [map_zsmul, zsmul_eq_mul] at h
    exact_mod_cast h
  have : NeZero (ℓ ^ (n + N)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  have h' : ℓ ^ (n + N) ∣ ℓ ^ N * a.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id]
    exact ha
  have h'' : ℓ ^ N * ℓ ^ n ∣ ℓ ^ N * a.val := by rwa [← pow_add, add_comm N n]
  exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hℓ.pos N) h''

end AddSubgroup
