/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Divisible
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The torsion of a divisible abelian group

If `D` is a divisible abelian group whose `ℓ`-torsion is finite of order `ℓ ^ r` for a prime
`ℓ`, then its `ℓ ^ n`-torsion is free of rank `r` over `ℤ / ℓ ^ n` for every `n`. This is
the structural input that makes the Tate module of an abelian variety a free `ℤ_[ℓ]`-module.

## Main statements

- `AddSubgroup.nonempty_addEquiv_torsionBy_of_natCard_eq`: `D[ℓ ^ n] ≃+ (Fin r → ZMod (ℓ ^ n))`.
- `AddSubgroup.nonempty_addEquiv_torsionBy_of_forall_prime`: if `|D[ℓ]| = ℓ ^ r` for every
  prime `ℓ ∣ n`, then `D[n] ≃+ (Fin r → ZMod n)`.
- `AddSubgroup.exists_exact_torsionBy_quotient`: for a subgroup `Λ` of an `n`-divisible group
  `G`, the exact sequence `0 → G[n] / Λ[n] → (G / Λ)[n] → Λ / nΛ → 0`.
- `AddMonoidHom.finite_quotient_range_zsmul_of_ker_le`: `A / nA` is finite if `A` maps to a
  finitely generated group with kernel divisible by `n`.

## Implementation notes

Instead of the classification of finite abelian `ℓ`-groups used in the blueprint, we choose an
`𝔽_ℓ`-basis `e` of `D[ℓ]`, lift it along multiplication by `ℓ ^ (n - 1)` to `y` using
divisibility, and show by induction on `n` that `c ↦ ∑ i, c i • y i` identifies
`(ℤ / ℓ ^ n) ^ r` with `D[ℓ ^ n]`.
-/

@[expose] public section

open scoped AddSubgroup

namespace AddSubgroup

section Map

variable {M N F : Type*} [AddCommGroup M] [AddCommGroup N] [FunLike F M N]
  [AddMonoidHomClass F M N]

/-- An additive homomorphism maps `n`-torsion to `n`-torsion. -/
theorem apply_mem_torsionBy (f : F) {n : ℤ} {x : M} (hx : x ∈ torsionBy M n) :
    f x ∈ torsionBy N n := by
  change n • f x = 0
  rw [← map_zsmul, show n • x = 0 from hx, map_zero]

/-- Multiplication by `l` maps `l ^ (n + 1)`-torsion to `l ^ n`-torsion. -/
theorem zsmul_mem_torsionBy_pow {l : ℤ} {n : ℕ} {x : M} (hx : x ∈ torsionBy M (l ^ (n + 1))) :
    l • x ∈ torsionBy M (l ^ n) := by
  change l ^ n • l • x = 0
  rw [smul_smul, ← pow_succ]
  exact hx

/-- An additive isomorphism restricts to an isomorphism of the `n`-torsion subgroups. -/
@[simps]
def torsionByCongr (e : M ≃+ N) (n : ℤ) : torsionBy M n ≃+ torsionBy N n where
  toFun x := ⟨e x.1, apply_mem_torsionBy e x.2⟩
  invFun y := ⟨e.symm y.1, apply_mem_torsionBy e.symm y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add e x.1 y.1)

/-- An additive isomorphism induces an isomorphism of the cokernels of multiplication by `n`. -/
noncomputable def quotientRangeZsmulCongr (e : M ≃+ N) (n : ℤ) :
    M ⧸ (zsmulAddGroupHom (α := M) n).range ≃+ N ⧸ (zsmulAddGroupHom (α := N) n).range :=
  QuotientAddGroup.congr _ _ e <| by
    ext y
    simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, zsmulAddGroupHom_apply]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, (map_zsmul e n x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨n • e.symm x, ⟨e.symm x, rfl⟩, by simp⟩

end Map

section IntProd

variable (G : Type*) [AddCommGroup G]

/-- The `n`-torsion of `ℤ × G` is the `n`-torsion of `G`, for `n ≠ 0`. -/
theorem nonempty_addEquiv_torsionBy_int_prod {n : ℤ} (hn : n ≠ 0) :
    Nonempty (torsionBy (ℤ × G) n ≃+ torsionBy G n) := by
  have h1 {x : ℤ × G} (hx : x ∈ torsionBy (ℤ × G) n) : x.1 = 0 := by
    have : n • x = 0 := hx
    have := congrArg Prod.fst this
    simpa [hn] using this
  have h2 {x : ℤ × G} (hx : x ∈ torsionBy (ℤ × G) n) : x.2 ∈ torsionBy G n :=
    congrArg Prod.snd (show n • x = 0 from hx)
  have h3 {y : G} (hy : y ∈ torsionBy G n) : ((0 : ℤ), y) ∈ torsionBy (ℤ × G) n := by
    change n • ((0 : ℤ), y) = 0
    rw [Prod.smul_mk, smul_zero, show n • y = 0 from hy]
    rfl
  exact ⟨{ toFun x := ⟨x.1.2, h2 x.2⟩
           invFun y := ⟨(0, y.1), h3 y.2⟩
           left_inv x := Subtype.ext (Prod.ext (h1 x.2).symm rfl)
           right_inv y := rfl
           map_add' x y := rfl }⟩

/-- If multiplication by `n ≠ 0` is surjective on `G`, then `(ℤ × G) / n (ℤ × G) ≅ ℤ / n`. -/
theorem nonempty_addEquiv_quotient_range_zsmul_int_prod {n : ℕ}
    (hG : Function.Surjective (zsmulAddGroupHom (α := G) n)) :
    Nonempty ((ℤ × G) ⧸ (zsmulAddGroupHom (α := ℤ × G) n).range ≃+ ZMod n) := by
  let φ : ℤ × G →+ ZMod n := (Int.castAddHom (ZMod n)).comp (AddMonoidHom.fst ℤ G)
  have hφ : Function.Surjective φ := fun a ↦ ⟨((a.cast : ℤ), 0), by simp [φ]⟩
  have hker : φ.ker = (zsmulAddGroupHom (α := ℤ × G) n).range := by
    ext ⟨a, g⟩
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.coe_fst, Int.coe_castAddHom, φ, AddMonoidHom.mem_range,
      zsmulAddGroupHom_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨b, rfl⟩
      obtain ⟨h, hh⟩ := hG g
      refine ⟨(b, h), Prod.ext ?_ hh⟩
      simp [mul_comm]
    · rintro ⟨⟨b, h⟩, he⟩
      have := congrArg Prod.fst he
      simp only [Prod.smul_mk, smul_eq_mul] at this
      exact ⟨b, by rw [← this, mul_comm]⟩
  rw [← hker]
  exact ⟨QuotientAddGroup.quotientKerEquivOfSurjective φ hφ⟩

end IntProd

section

variable {D ι : Type*} [AddCommGroup D] [Fintype ι]

/-- Let `e` be a family in an abelian group which is a "basis of the `ℓ`-torsion with integer
coefficients", i.e. integer relations among the `e i` have coefficients divisible by `ℓ`, and
every element killed by `ℓ` is an integer combination of the `e i`. If `ℓ ^ k • z i = e i`,
then integer relations among the `z i` have coefficients divisible by `ℓ ^ (k + 1)`, and every
element killed by `ℓ ^ (k + 1)` is an integer combination of the `z i`. -/
theorem sum_zsmul_dvd_and_exists_of_pow_zsmul_eq (ℓ : ℤ) (e : ι → D)
    (he : ∀ c : ι → ℤ, ∑ i, c i • e i = 0 → ∀ i, ℓ ∣ c i)
    (he' : ∀ x : D, ℓ • x = 0 → ∃ c : ι → ℤ, x = ∑ i, c i • e i) (k : ℕ) (z : ι → D)
    (hz : ∀ i, ℓ ^ k • z i = e i) :
    (∀ c : ι → ℤ, ∑ i, c i • z i = 0 → ∀ i, ℓ ^ (k + 1) ∣ c i) ∧
      ∀ x : D, ℓ ^ (k + 1) • x = 0 → ∃ c : ι → ℤ, x = ∑ i, c i • z i := by
  induction k generalizing z with
  | zero =>
    obtain rfl : z = e := funext fun i ↦ by simpa using hz i
    simpa using ⟨he, he'⟩
  | succ k ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (fun i ↦ ℓ • z i) fun i ↦ by rw [smul_smul, ← pow_succ, hz]
    refine ⟨fun c hc ↦ ?_, fun x hx ↦ ?_⟩
    · have h₁ : ∀ i, ℓ ∣ c i := he c <| by
        simp_rw [← hz, smul_comm (c _), ← Finset.smul_sum, hc, smul_zero]
      choose d hd using h₁
      have h₂ := ih₁ d <| by
        simp_rw [smul_smul, mul_comm _ ℓ, ← hd, hc]
      intro i
      rw [hd i, pow_succ' ℓ (k + 1)]
      exact mul_dvd_mul_left ℓ (h₂ i)
    · obtain ⟨c, hc⟩ := ih₂ (ℓ • x) <| by rw [smul_smul, ← pow_succ, hx]
      obtain ⟨a, ha⟩ := he' (x - ∑ i, c i • z i) <| by
        rw [smul_sub, hc, Finset.smul_sum]
        simp_rw [smul_comm ℓ (c _), sub_self]
      refine ⟨fun i ↦ c i + a i * ℓ ^ (k + 1), ?_⟩
      simp_rw [add_smul, Finset.sum_add_distrib, mul_smul, hz, ← ha]
      abel

end

/-- If the `ℓ`-torsion of an abelian group `D` has order `ℓ ^ r`, then it has an "integral
basis": a family `e : Fin r → D` of `ℓ`-torsion elements such that integer relations among the
`e i` have coefficients divisible by `ℓ`, and every element killed by `ℓ` is an integer
combination of the `e i`. -/
theorem exists_basis_torsionBy (D : Type*) [AddCommGroup D] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)
    (hr : Nat.card D[(ℓ : ℤ)] = ℓ ^ r) :
    ∃ e : Fin r → D, (∀ i, (ℓ : ℤ) • e i = 0) ∧
      (∀ c : Fin r → ℤ, ∑ i, c i • e i = 0 → ∀ i, (ℓ : ℤ) ∣ c i) ∧
      ∀ x : D, (ℓ : ℤ) • x = 0 → ∃ c : Fin r → ℤ, x = ∑ i, c i • e i := by
  have hℓ : ℓ.Prime := Fact.out
  -- an `𝔽_ℓ`-basis `e` of `D[ℓ]`
  let _ : Module (ZMod ℓ) D[(ℓ : ℤ)] := torsionBy.zmodModule
  have : Finite D[(ℓ : ℤ)] :=
    Nat.finite_of_card_ne_zero (by rw [hr]; exact pow_ne_zero _ hℓ.ne_zero)
  have : Fintype D[(ℓ : ℤ)] := Fintype.ofFinite _
  have hrank : Module.finrank (ZMod ℓ) D[(ℓ : ℤ)] = r := by
    have h := Module.card_eq_pow_finrank (K := ZMod ℓ) (V := D[(ℓ : ℤ)])
    rw [← Nat.card_eq_fintype_card, hr, ZMod.card] at h
    exact (Nat.pow_right_injective hℓ.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod ℓ) D[(ℓ : ℤ)] hrank
  let e : Fin r → D := fun i ↦ b i
  have he : ∀ c : Fin r → ℤ, ∑ i, c i • e i = 0 → ∀ i, (ℓ : ℤ) ∣ c i := by
    intro c hc i
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 <|
      Fintype.linearIndependent_iff.1 b.linearIndependent (fun i ↦ (c i : ZMod ℓ))
        (Subtype.ext ?_) i
    simpa [Int.cast_smul_eq_zsmul] using hc
  have he' : ∀ x : D, (ℓ : ℤ) • x = 0 → ∃ c : Fin r → ℤ, x = ∑ i, c i • e i := by
    intro x hx
    refine ⟨fun i ↦ (b.repr ⟨x, hx⟩ i).cast, ?_⟩
    conv_lhs => rw [show x = ((⟨x, hx⟩ : D[(ℓ : ℤ)]) : D) from rfl, ← b.sum_repr ⟨x, hx⟩]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    conv_lhs => rw [← ZMod.intCast_zmod_cast (b.repr ⟨x, hx⟩ i), Int.cast_smul_eq_zsmul]
    rfl
  exact ⟨e, fun i ↦ (Submodule.mem_torsionBy_iff _ _).1 (b i).2, he, he'⟩

/-- Blueprint `proposition-integral-tate-module--1`: The torsion of a divisible group.

This is also the blueprint lemma `proposition-integral-tate-module--1`.

Let `D` be a divisible abelian group, let `ℓ` be a prime and suppose that the `ℓ`-torsion of
`D` is finite of order `ℓ ^ r`. Then for every `n` the `ℓ ^ n`-torsion of `D` is isomorphic
to `(ℤ / ℓ ^ n) ^ r`. -/
theorem nonempty_addEquiv_torsionBy_of_natCard_eq (D : Type*) [AddCommGroup D]
    [DivisibleBy D ℤ] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (hr : Nat.card D[(ℓ : ℤ)] = ℓ ^ r) (n : ℕ) :
    Nonempty (D[((ℓ : ℤ) ^ n)] ≃+ (Fin r → ZMod (ℓ ^ n))) := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨e, he₀, he, he'⟩ := exists_basis_torsionBy D ℓ r hr
  cases n with
  | zero =>
    rw [pow_zero, pow_zero]
    have : Subsingleton D[(1 : ℤ)] := ⟨fun x y ↦ Subtype.ext <| by
      have hx := (Submodule.mem_torsionBy_iff _ _).1 x.2
      have hy := (Submodule.mem_torsionBy_iff _ _).1 y.2
      rw [one_smul] at hx hy
      rw [hx, hy]⟩
    exact ⟨(AddEquiv.ofBijective (0 : D[(1 : ℤ)] →+ (Fin r → ZMod 1))
      ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩)⟩
  | succ m =>
    -- lifts `y i` of `e i` along multiplication by `ℓ ^ m`
    let y : Fin r → D := fun i ↦ DivisibleBy.div (e i) ((ℓ : ℤ) ^ m)
    have hy : ∀ i, (ℓ : ℤ) ^ m • y i = e i := fun i ↦
      DivisibleBy.div_cancel _ (pow_ne_zero _ (Int.natCast_ne_zero.2 hℓ.ne_zero))
    obtain ⟨hinj, hsurj⟩ := sum_zsmul_dvd_and_exists_of_pow_zsmul_eq _ e he he' m y hy
    rw [show (ℓ : ℤ) ^ (m + 1) = ((ℓ ^ (m + 1) : ℕ) : ℤ) by push_cast; rfl]
    let _ : Module (ZMod (ℓ ^ (m + 1))) D[((ℓ ^ (m + 1) : ℕ) : ℤ)] := torsionBy.zmodModule
    have hyN : ∀ i, y i ∈ D[((ℓ ^ (m + 1) : ℕ) : ℤ)] := fun i ↦ by
      refine (Submodule.mem_torsionBy_iff _ _).2 ?_
      push_cast
      rw [pow_succ', mul_smul, hy]
      exact (Submodule.mem_torsionBy_iff _ _).2 (he₀ i)
    let f := Fintype.linearCombination (ZMod (ℓ ^ (m + 1))) fun i ↦
      (⟨y i, hyN i⟩ : D[((ℓ ^ (m + 1) : ℕ) : ℤ)])
    have hf : ∀ c : Fin r → ℤ, (f fun i ↦ (c i : ZMod (ℓ ^ (m + 1))) : D) = ∑ i, c i • y i := by
      intro c
      simp [f, Fintype.linearCombination_apply, Int.cast_smul_eq_zsmul]
    have hf_inj : Function.Injective f := by
      refine (injective_iff_map_eq_zero f).2 fun c hc ↦ funext fun i ↦ ?_
      rw [← funext fun i ↦ ZMod.intCast_zmod_cast (c i)] at hc ⊢
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ?_
      push_cast
      have hc' := congrArg Subtype.val hc
      rw [hf] at hc'
      exact hinj _ hc' i
    have hf_surj : Function.Surjective f := by
      rintro ⟨x, hx⟩
      have hx' := (Submodule.mem_torsionBy_iff _ _).1 hx
      push_cast at hx'
      obtain ⟨c, rfl⟩ := hsurj x hx'
      exact ⟨fun i ↦ c i, Subtype.ext (hf c)⟩
    exact ⟨(AddEquiv.ofBijective f.toAddMonoidHom ⟨hf_inj, hf_surj⟩).symm⟩

/-- For coprime `a` and `b`, the `a * b`-torsion of an abelian group is the product of its
`a`-torsion and its `b`-torsion, via `x ↦ (b • x, a • x)`. -/
theorem nonempty_addEquiv_torsionBy_mul_prod (D : Type*) [AddCommGroup D] {a b : ℕ}
    (hab : a.Coprime b) :
    Nonempty (D[((a * b : ℕ) : ℤ)] ≃+ D[(a : ℤ)] × D[(b : ℤ)]) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  let f : D[((a * b : ℕ) : ℤ)] →+ D[(a : ℤ)] × D[(b : ℤ)] :=
    { toFun x := (⟨(b : ℤ) • x.1, by
          have := (Submodule.mem_torsionBy_iff _ _).1 x.2
          refine (Submodule.mem_torsionBy_iff _ _).2 ?_
          rw [smul_smul, ← this]
          push_cast
          ring_nf⟩,
        ⟨(a : ℤ) • x.1, by
          have := (Submodule.mem_torsionBy_iff _ _).1 x.2
          refine (Submodule.mem_torsionBy_iff _ _).2 ?_
          rw [smul_smul, ← this]
          push_cast
          ring_nf⟩)
      map_zero' := by ext <;> simp
      map_add' x y := by ext <;> simp }
  refine ⟨AddEquiv.ofBijective f ⟨(injective_iff_map_eq_zero f).2 fun x hx ↦ ?_, ?_⟩⟩
  · have h₁ : (b : ℤ) • (x : D) = 0 := congrArg (fun y ↦ (y.1 : D)) hx
    have h₂ : (a : ℤ) • (x : D) = 0 := congrArg (fun y ↦ (y.2 : D)) hx
    refine Subtype.ext ?_
    rw [ZeroMemClass.coe_zero, ← one_smul ℤ (x : D), ← huv, add_smul, mul_smul, mul_smul, h₁, h₂,
      smul_zero, smul_zero, add_zero]
  · rintro ⟨y, z⟩
    have hy := (Submodule.mem_torsionBy_iff _ _).1 y.2
    have hz := (Submodule.mem_torsionBy_iff _ _).1 z.2
    refine ⟨⟨v • (y : D) + u • (z : D), (Submodule.mem_torsionBy_iff _ _).2 ?_⟩, ?_⟩
    · push_cast
      rw [smul_add, smul_smul, smul_smul, show (a : ℤ) * b * v = b * v * a by ring,
        show (a : ℤ) * b * u = a * u * b by ring, mul_smul, mul_smul (a * u), hy, hz, smul_zero,
        smul_zero, add_zero]
    · have hy' : (y : D) = (v * b) • (y : D) := by
        conv_lhs => rw [← one_smul ℤ (y : D), ← huv]
        rw [add_smul, mul_smul u, hy, smul_zero, zero_add]
      have hz' : (z : D) = (u * a) • (z : D) := by
        conv_lhs => rw [← one_smul ℤ (z : D), ← huv]
        rw [add_smul, mul_smul v, hz, smul_zero, add_zero]
      ext
      · change (b : ℤ) • (v • (y : D) + u • (z : D)) = y
        rw [smul_add, smul_smul, smul_smul, mul_comm (b : ℤ) u, mul_smul u, hz, smul_zero,
          add_zero, mul_comm, ← hy']
      · change (a : ℤ) • (v • (y : D) + u • (z : D)) = z
        rw [smul_add, smul_smul, smul_smul, mul_comm (a : ℤ) v, mul_smul v, hy, smul_zero,
          zero_add, mul_comm, ← hz']

/-- The Chinese remainder step of blueprint `proposition-multiplication-n--2`.

Let `D` be a divisible abelian group and suppose that for every prime `ℓ` dividing `n ≠ 0` the
`ℓ`-torsion of `D` has order `ℓ ^ r`. Then the `n`-torsion of `D` is isomorphic to
`(ℤ / n) ^ r`: for prime powers this is
`AddSubgroup.nonempty_addEquiv_torsionBy_of_natCard_eq`, and the general case follows by the
Chinese remainder theorem. -/
theorem nonempty_addEquiv_torsionBy_of_forall_prime (D : Type*) [AddCommGroup D]
    [DivisibleBy D ℤ] (r : ℕ) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → Nat.card D[(ℓ : ℤ)] = ℓ ^ r) :
    Nonempty (D[(n : ℤ)] ≃+ (Fin r → ZMod n)) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow ℓ e hℓ he =>
    have : Fact ℓ.Prime := ⟨hℓ⟩
    push_cast
    exact nonempty_addEquiv_torsionBy_of_natCard_eq D ℓ r (h ℓ hℓ (dvd_pow_self ℓ he.ne')) e
  | zero => exact absurd rfl hn
  | one =>
    have : Subsingleton D[((1 : ℕ) : ℤ)] := ⟨fun x y ↦ Subtype.ext <| by
      have hx := (Submodule.mem_torsionBy_iff _ _).1 x.2
      have hy := (Submodule.mem_torsionBy_iff _ _).1 y.2
      simp only [Nat.cast_one, one_smul] at hx hy
      rw [hx, hy]⟩
    exact ⟨AddEquiv.ofBijective (0 : D[((1 : ℕ) : ℤ)] →+ (Fin r → ZMod 1))
      ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨ea⟩ := iha (by omega) fun ℓ hℓ hd ↦ h ℓ hℓ (hd.mul_right b)
    obtain ⟨eb⟩ := ihb (by omega) fun ℓ hℓ hd ↦ h ℓ hℓ (hd.mul_left a)
    obtain ⟨e⟩ := nonempty_addEquiv_torsionBy_mul_prod D hab
    let arrow : (Fin r → ZMod a) × (Fin r → ZMod b) ≃+ (Fin r → ZMod a × ZMod b) :=
      { (Equiv.arrowProdEquivProdArrow _ _ _).symm with map_add' := fun _ _ ↦ rfl }
    exact ⟨e.trans ((ea.prodCongr eb).trans (arrow.trans
      (AddEquiv.piCongrRight fun _ ↦ (ZMod.chineseRemainder hab).toAddEquiv).symm))⟩

section Quotient

variable {G : Type*} [AddCommGroup G]

/-- **Torsion in a quotient of a divisible group.** Let `Λ` be a subgroup of an abelian group
`G` on which multiplication by `n` is surjective. Then there is a short exact sequence
`0 → G[n] / Λ[n] → (G / Λ)[n] → Λ / nΛ → 0`, whose second map sends the class of `g` with
`n • g ∈ Λ` to the class of `n • g`.
(blueprint: `proposition-cohomology-smooth-affine-curve--3`) -/
theorem exists_exact_torsionBy_quotient (Λ : AddSubgroup G) (n : ℤ)
    (hG : Function.Surjective (zsmulAddGroupHom (α := G) n)) :
    ∃ (α : G[n] ⧸ Λ.addSubgroupOf G[n] →+ (G ⧸ Λ)[n])
      (δ : (G ⧸ Λ)[n] →+ Λ ⧸ (zsmulAddGroupHom (α := Λ) n).range),
      Function.Injective α ∧ Function.Exact α δ ∧ Function.Surjective δ ∧
        ∀ (x : (G ⧸ Λ)[n]) (g : G), (g : G ⧸ Λ) = x →
          ∃ hg : n • g ∈ Λ, δ x = QuotientAddGroup.mk (⟨n • g, hg⟩ : Λ) := by
  classical
  -- the map `G[n] → (G/Λ)[n]`
  let ι : G[n] →+ (G ⧸ Λ)[n] :=
    { toFun x := ⟨(x.1 : G ⧸ Λ), (Submodule.mem_torsionBy_iff _ _).2 <| by
        rw [← QuotientAddGroup.mk_zsmul, (Submodule.mem_torsionBy_iff _ _).1 x.2]; rfl⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hker : ι.ker = Λ.addSubgroupOf G[n] := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, Subtype.ext_iff]
    exact QuotientAddGroup.eq_zero_iff _
  let α := QuotientAddGroup.lift (Λ.addSubgroupOf G[n]) ι (hker ▸ le_rfl)
  -- the connecting map
  have hmem (x : (G ⧸ Λ)[n]) (g : G) (hg : (g : G ⧸ Λ) = x) : n • g ∈ Λ := by
    have := (Submodule.mem_torsionBy_iff _ _).1 x.2
    rw [← hg, ← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff] at this
    exact this
  let lift (x : (G ⧸ Λ)[n]) : G := (QuotientAddGroup.mk_surjective x.1).choose
  have hlift (x : (G ⧸ Λ)[n]) : (lift x : G ⧸ Λ) = x :=
    (QuotientAddGroup.mk_surjective x.1).choose_spec
  let N := (zsmulAddGroupHom (α := Λ) n).range
  have key (x : (G ⧸ Λ)[n]) (g g' : G) (hg : (g : G ⧸ Λ) = x) (hg' : (g' : G ⧸ Λ) = x) :
      (QuotientAddGroup.mk (⟨n • g, hmem x g hg⟩ : Λ) : Λ ⧸ N) =
        QuotientAddGroup.mk (⟨n • g', hmem x g' hg'⟩ : Λ) := by
    rw [QuotientAddGroup.eq]
    have h : -g + g' ∈ Λ := by
      rw [← QuotientAddGroup.eq, hg, hg']
    refine ⟨⟨-g + g', h⟩, ?_⟩
    ext
    simp [smul_add, smul_neg]
  let δ : (G ⧸ Λ)[n] →+ Λ ⧸ N :=
    { toFun x := QuotientAddGroup.mk (⟨n • lift x, hmem x _ (hlift x)⟩ : Λ)
      map_zero' := by
        rw [key 0 (lift 0) 0 (hlift 0) (by simp), QuotientAddGroup.eq_zero_iff]
        exact ⟨0, by ext; simp⟩
      map_add' x y := by
        rw [key (x + y) (lift (x + y)) (lift x + lift y) (hlift _)
          (by simp [hlift])]
        rw [← QuotientAddGroup.mk_add]
        congr 1
        ext
        simp [smul_add] }
  have hδ (x : (G ⧸ Λ)[n]) (g : G) (hg : (g : G ⧸ Λ) = x) :
      δ x = QuotientAddGroup.mk (⟨n • g, hmem x g hg⟩ : Λ) :=
    key x _ _ (hlift x) hg
  refine ⟨α, δ, ?_, ?_, ?_, fun x g hg ↦ ⟨hmem x g hg, hδ x g hg⟩⟩
  · rw [← AddMonoidHom.ker_eq_bot_iff, QuotientAddGroup.ker_lift, hker]
    simp
  · intro x
    constructor
    · intro hx
      rw [hδ x _ (hlift x), QuotientAddGroup.eq_zero_iff] at hx
      obtain ⟨l, hl⟩ := hx
      refine ⟨QuotientAddGroup.mk ⟨lift x - l, (Submodule.mem_torsionBy_iff _ _).2 ?_⟩, ?_⟩
      · have := congrArg Subtype.val hl
        simp only [zsmulAddGroupHom_apply, AddSubgroup.coe_zsmul] at this
        rw [smul_sub, this, sub_self]
      · ext
        change ((lift x - l : G) : G ⧸ Λ) = x
        rw [QuotientAddGroup.mk_sub, hlift x, (QuotientAddGroup.eq_zero_iff _).2 l.2, sub_zero]
    · rintro ⟨y, rfl⟩
      induction y using QuotientAddGroup.induction_on with
      | H y =>
      rw [hδ _ y.1 rfl, QuotientAddGroup.eq_zero_iff]
      refine ⟨0, ?_⟩
      ext
      simp [(Submodule.mem_torsionBy_iff _ _).1 y.2]
  · intro z
    induction z using QuotientAddGroup.induction_on with
    | H l =>
    obtain ⟨g, hg⟩ := hG l
    refine ⟨⟨(g : G ⧸ Λ), (Submodule.mem_torsionBy_iff _ _).2 ?_⟩, ?_⟩
    · rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
      simp only [zsmulAddGroupHom_apply] at hg
      rw [hg]; exact l.2
    · rw [hδ _ g rfl]
      congr 1
      ext
      simpa using hg


/-- Let `Λ` be a finitely generated subgroup of an abelian group `G` on which multiplication by
`n ≠ 0` is surjective, and assume that `G[n]` is finite. Then `(G / Λ)[n]` is finite: it is an
extension of the finite group `Λ / nΛ` by a quotient of `G[n]`
(`AddSubgroup.exists_exact_torsionBy_quotient`). -/
theorem finite_torsionBy_quotient (Λ : AddSubgroup G) {n : ℕ} (hn : n ≠ 0)
    (hG : Function.Surjective (zsmulAddGroupHom (α := G) n)) [Finite G[n]] (hΛ : Λ.FG) :
    Finite (G ⧸ Λ)[n] := by
  obtain ⟨α, δ, -, hαδ, hδ, -⟩ := exists_exact_torsionBy_quotient Λ n hG
  let N := (zsmulAddGroupHom (α := Λ) n).range
  have : AddGroup.FG Λ := (AddGroup.fg_iff_addSubgroup_fg Λ).2 hΛ
  have : Module.Finite ℤ (Λ ⧸ N) := by
    rw [Module.Finite.iff_addGroup_fg]
    exact AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective N)
  have : Finite (Λ ⧸ N) := Module.finite_of_fg_torsion _ fun x ↦ by
    induction x using QuotientAddGroup.induction_on with
    | H l =>
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩, ?_⟩
    change (n : ℤ) • (QuotientAddGroup.mk l : Λ ⧸ N) = 0
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨l, rfl⟩
  have : Finite α.range := Set.finite_range _
  have : Finite ((G ⧸ Λ)[n] ⧸ α.range) := by
    have h : α.range = δ.ker := by
      ext x; exact (hαδ x).symm
    rw [h]
    exact .of_equiv _ (QuotientAddGroup.quotientKerEquivOfSurjective δ hδ).toEquiv.symm
  exact .of_addSubgroup_quotient (H := α.range)

end Quotient

end AddSubgroup

/-- Let `D : A →+ F` be a homomorphism of abelian groups with `F` finitely generated, and `n ≠ 0`.
If every element of the kernel of `D` is divisible by `n`, then `A / nA` is finite: it embeds
into `D(A) / n D(A)`, a finitely generated `n`-torsion group. -/
theorem AddMonoidHom.finite_quotient_range_zsmul_of_ker_le {A F : Type*} [AddCommGroup A]
    [AddCommGroup F] [Module.Finite ℤ F] (D : A →+ F) {n : ℕ} (hn : n ≠ 0)
    (hker : D.ker ≤ (zsmulAddGroupHom (α := A) n).range) :
    Finite (A ⧸ (zsmulAddGroupHom (α := A) n).range) := by
  set N := (zsmulAddGroupHom (α := A) n).range
  set Λ := D.range
  set M := (zsmulAddGroupHom (α := Λ) n).range
  have : Module.Finite ℤ Λ :=
    Module.Finite.iff_fg.2 (IsNoetherian.noetherian (AddSubgroup.toIntSubmodule Λ))
  have : Module.Finite ℤ (Λ ⧸ M) := by
    rw [Module.Finite.iff_addGroup_fg]
    have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
    exact AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective M)
  have : Finite (Λ ⧸ M) := Module.finite_of_fg_torsion _ fun x ↦ by
    induction x using QuotientAddGroup.induction_on with
    | H l =>
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩, ?_⟩
    change (n : ℤ) • (QuotientAddGroup.mk l : Λ ⧸ M) = 0
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨l, rfl⟩
  let φ : A →+ Λ ⧸ M := (QuotientAddGroup.mk' M).comp D.rangeRestrict
  have hN : N ≤ φ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker]
    change (QuotientAddGroup.mk (D.rangeRestrict ((n : ℤ) • a)) : Λ ⧸ M) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨D.rangeRestrict a, by simp⟩
  refine Finite.of_injective (QuotientAddGroup.lift N φ hN) ?_
  rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H a =>
  rw [AddMonoidHom.mem_ker, QuotientAddGroup.lift_mk] at hx
  change (QuotientAddGroup.mk (D.rangeRestrict a) : Λ ⧸ M) = 0 at hx
  rw [QuotientAddGroup.eq_zero_iff] at hx
  obtain ⟨⟨_, b, rfl⟩, hb⟩ := hx
  have hb' : D ((n : ℤ) • b) = D a := by
    rw [map_zsmul]; exact congrArg Subtype.val hb
  obtain ⟨c, hc⟩ := hker (show a - (n : ℤ) • b ∈ D.ker by
    rw [AddMonoidHom.mem_ker, map_sub, hb', sub_self])
  rw [AddSubgroup.mem_bot, QuotientAddGroup.eq_zero_iff]
  refine ⟨c + b, ?_⟩
  simp only [zsmulAddGroupHom_apply] at hc ⊢
  rw [smul_add, hc, sub_add_cancel]

namespace AddSubgroup

section HerbrandQuotient

variable {Y : Type*} [AddCommGroup Y]

/-- `|X / nX|` is the relative index of `nX` in `X`. -/
theorem natCard_quotient_range_zsmul_eq_relIndex (X : AddSubgroup Y) (n : ℤ) :
    Nat.card (X ⧸ (zsmulAddGroupHom (α := X) n).range) =
      (X.map (zsmulAddGroupHom (α := Y) n)).relIndex X := by
  rw [relIndex, index_eq_card]
  congr 3
  ext ⟨x, hx⟩
  simp only [mem_addSubgroupOf, mem_map, zsmulAddGroupHom_apply, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.1, y.2, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- **Multiplicativity of the Herbrand-type quotient of multiplication by `n`.** For a subgroup
`X` of an abelian group `Y` with quotient `Z = Y ⧸ X` and `n : ℤ`,
`|X / nX| · |Z / nZ| · |Y[n]| = |Y / nY| · |X[n]| · |Z[n]|` (as natural numbers, with the
convention that infinite cardinals are `0`). This is the snake lemma for multiplication by `n` on
`0 → X → Y → Z → 0`. -/
theorem natCard_quotient_range_zsmul_mul_eq (X : AddSubgroup Y) (n : ℤ) :
    Nat.card (X ⧸ (zsmulAddGroupHom (α := X) n).range) *
        Nat.card ((Y ⧸ X) ⧸ (zsmulAddGroupHom (α := Y ⧸ X) n).range) *
        Nat.card (torsionBy Y n) =
      Nat.card (Y ⧸ (zsmulAddGroupHom (α := Y) n).range) * Nat.card (torsionBy X n) *
        Nat.card (torsionBy (Y ⧸ X) n) := by
  set φ := zsmulAddGroupHom (α := Y) n
  set T := φ.ker
  set Xn := X.comap φ
  have hT : torsionBy Y n = T := by
    ext y
    simp [T, φ, Submodule.mem_torsionBy_iff]
  -- `|Z / nZ| = [Y : nY + X]`
  have hB : Nat.card ((Y ⧸ X) ⧸ (zsmulAddGroupHom (α := Y ⧸ X) n).range) =
      (φ.range ⊔ X).index := by
    rw [← index_eq_card, ← index_comap_of_surjective _ (QuotientAddGroup.mk'_surjective X)]
    congr 1
    ext y
    simp only [mem_comap, AddMonoidHom.mem_range, zsmulAddGroupHom_apply,
      QuotientAddGroup.mk'_apply, mem_sup]
    constructor
    · rintro ⟨z, hz⟩
      induction z using QuotientAddGroup.induction_on with
      | H z =>
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq] at hz
      exact ⟨n • z, ⟨z, rfl⟩, -(n • z) + y, hz, by abel⟩
    · rintro ⟨_, ⟨z, rfl⟩, x, hx, rfl⟩
      refine ⟨z, ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq]
      simpa [φ] using hx
  -- `|Z[n]| = [n⁻¹X : X]`
  have hZ : Nat.card (torsionBy (Y ⧸ X) n) = X.relIndex Xn := by
    let ψ : Xn →+ torsionBy (Y ⧸ X) n :=
      { toFun y := ⟨y.1, by
          change n • (y.1 : Y ⧸ X) = 0
          rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
          exact y.2⟩
        map_zero' := rfl
        map_add' _ _ := rfl }
    have hψ : Function.Surjective ψ := by
      rintro ⟨z, hz⟩
      induction z using QuotientAddGroup.induction_on with
      | H z =>
      refine ⟨⟨z, ?_⟩, rfl⟩
      change n • (z : Y ⧸ X) = 0 at hz
      rwa [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff] at hz
    have hker : ψ.ker = X.addSubgroupOf Xn := by
      ext y
      simp [ψ, mem_addSubgroupOf]
    rw [relIndex, index_eq_card, ← hker]
    exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv).symm
  -- `|Y[n]| = [Y[n] : X[n]] · |X[n]|`
  have hX : Nat.card (torsionBy X n) = Nat.card (X.addSubgroupOf T) := by
    refine Nat.card_congr
      { toFun y := ⟨⟨y.1.1, congrArg Subtype.val (show n • y.1 = 0 from y.2)⟩, y.1.2⟩
        invFun y := ⟨⟨y.1.1, y.2⟩, Subtype.ext (show n • y.1.1 = 0 from y.1.2)⟩
        left_inv _ := rfl
        right_inv _ := rfl }
  have hY : Nat.card (torsionBy Y n) = X.relIndex T * Nat.card (torsionBy X n) := by
    rw [hT, hX, relIndex, mul_comm, card_mul_index]
  rw [natCard_quotient_range_zsmul_eq_relIndex, hB, hZ, hY, ← index_eq_card]
  -- index computations inside `Y`
  have h1 : φ.range.index = φ.range.relIndex X * (φ.range ⊔ X).index := by
    rw [← relIndex_sup_left, relIndex_mul_index le_sup_left]
  have h2 : (X.map φ).relIndex X = (X ⊔ T).relIndex Xn * φ.range.relIndex X := by
    have hle : X.map φ ≤ φ.range ⊓ X := le_inf (map_le_range φ X) fun _ ⟨y, hy, e⟩ ↦
      e ▸ X.zsmul_mem hy n
    rw [← relIndex_mul_relIndex _ _ _ hle inf_le_right, inf_relIndex_right, ← comap_map_eq,
      relIndex_comap, map_comap_eq]
  have h3 : X.relIndex Xn = X.relIndex T * (X ⊔ T).relIndex Xn := by
    have hXT : X ⊔ T ≤ Xn := sup_le (fun y hy ↦ X.zsmul_mem hy n) fun y hy ↦ by
      change n • y ∈ X
      rw [show n • y = 0 from hy]
      exact X.zero_mem
    rw [← relIndex_sup_left T X, relIndex_mul_relIndex _ _ _ le_sup_left hXT]
  rw [h1, h2, h3]
  ring


/-- If the kernel of `D : A →+ B` consists of multiples of `n`, then `A / nA ≅ D(A) / n D(A)`. -/
theorem natCard_quotient_range_zsmul_eq_of_ker_le {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (D : A →+ B) (n : ℤ) (hker : D.ker ≤ (zsmulAddGroupHom (α := A) n).range) :
    Nat.card (A ⧸ (zsmulAddGroupHom (α := A) n).range) =
      Nat.card (D.range ⧸ (zsmulAddGroupHom (α := D.range) n).range) := by
  let φ : A →+ D.range ⧸ (zsmulAddGroupHom (α := D.range) n).range :=
    (QuotientAddGroup.mk' _).comp D.rangeRestrict
  have hφ : Function.Surjective φ :=
    (QuotientAddGroup.mk'_surjective _).comp D.rangeRestrict_surjective
  have hker' : φ.ker = (zsmulAddGroupHom (α := A) n).range := by
    ext a
    simp only [φ, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range, zsmulAddGroupHom_apply]
    constructor
    · rintro ⟨⟨_, b, rfl⟩, hb⟩
      have hb' : D (n • b) = D a := by
        rw [map_zsmul]
        exact congrArg Subtype.val hb
      obtain ⟨c, hc⟩ := hker (show a - n • b ∈ D.ker by
        rw [AddMonoidHom.mem_ker, map_sub, hb', sub_self])
      refine ⟨c + b, ?_⟩
      simp only [zsmulAddGroupHom_apply] at hc
      rw [smul_add, hc, sub_add_cancel]
    · rintro ⟨b, rfl⟩
      exact ⟨D.rangeRestrict b, by simp⟩
  rw [← hker']
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).toEquiv

/-- The order of the middle term of an exact sequence `A → H → B`. -/
theorem natCard_eq_of_exact {A H B : Type*} [AddCommGroup A] [AddCommGroup H] [AddCommGroup B]
    {α : A →+ H} {β : H →+ B} (hαβ : Function.Exact α β) :
    Nat.card H = Nat.card (A ⧸ α.ker) * Nat.card β.range := by
  have hk : β.ker = α.range := by
    ext x
    exact hαβ x
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup β.ker, mul_comm,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange β).toEquiv, hk,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange α).toEquiv]

/-- `ℤ^S / n ℤ^S` has order `n ^ |S|`. -/
theorem natCard_quotient_range_zsmul_pi {S : Type*} [Finite S] (n : ℕ) :
    Nat.card ((S → ℤ) ⧸ (zsmulAddGroupHom (α := S → ℤ) n).range) = n ^ Nat.card S := by
  let φ : (S → ℤ) →+ (S → ZMod n) :=
    { toFun v s := v s
      map_zero' := by ext; simp
      map_add' _ _ := by ext; simp }
  have hφ : Function.Surjective φ := fun v ↦ ⟨fun s ↦ (v s).cast, by ext s; simp [φ]⟩
  have hker : φ.ker = (zsmulAddGroupHom (α := S → ℤ) n).range := by
    ext v
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, zsmulAddGroupHom_apply]
    constructor
    · intro h
      refine ⟨fun s ↦ v s / n, funext fun s ↦ ?_⟩
      have h' : ((v s : ℤ) : ZMod n) = 0 := congr_fun h s
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
      simp only [Pi.smul_apply, smul_eq_mul]
      exact Int.mul_ediv_cancel' h'
    · rintro ⟨w, rfl⟩
      ext s
      simp [φ]
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
    Nat.card_fun, Nat.card_zmod]

/-- `ℤ^S` has no `n`-torsion for `n ≠ 0`, hence neither has any subgroup of it. -/
theorem natCard_torsionBy_eq_one_of_le_pi {S : Type*} (X : AddSubgroup (S → ℤ)) {n : ℤ}
    (hn : n ≠ 0) : Nat.card (torsionBy X n) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y ↦ ?_⟩, ⟨0⟩⟩
  have h (z : torsionBy X n) : z = 0 := by
    have hz : n • z.1.1 = 0 := congrArg Subtype.val z.2
    refine Subtype.ext (Subtype.ext (funext fun s ↦ ?_))
    have := congr_fun hz s
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero, hn, false_or] at this
    exact this
  rw [h x, h y]

end HerbrandQuotient

end AddSubgroup
