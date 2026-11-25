/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic
public import WeilConjectures.Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Integral and rational Tate modules

Let `ℓ` be a prime and `M` an abelian group. Writing `M[ℓ ^ n]` for the `ℓ ^ n`-torsion of `M`,
the *(integral) Tate module* of `M` is the inverse limit

```
T_ℓ M = {(t n) ∈ ∏ n, M[ℓ ^ n] | ∀ n, ℓ • t (n + 1) = t n}
```

taken along multiplication by `ℓ`. It is realised here as an `AddSubgroup` of the product
`∀ n : ℕ, M`, cut out by the two conditions `ℓ ^ n • t n = 0` and `ℓ • t (n + 1) = t n`. It
carries a natural `ℤ_[ℓ]`-action, in which an `ℓ`-adic integer `a` acts on the `n`-th coordinate
through the integer `PadicInt.appr a n`, a representative of `a` modulo `ℓ ^ n`; the *rational
Tate module* is the `ℚ_[ℓ]`-vector space `V_ℓ M = ℚ_[ℓ] ⊗_{ℤ_[ℓ]} T_ℓ M`.

## Main definitions

- `AddCommGroup.tateModule`: the integral Tate module `T_ℓ M`.
- `AddCommGroup.tateModule.instModule`: its `ℤ_[ℓ]`-module structure.
- `AddCommGroup.rationalTateModule`: the rational Tate module `V_ℓ M`.
- `AddCommGroup.tateModule.map`, `AddCommGroup.rationalTateModule.map`: the maps induced by a
  homomorphism `M →+ N`.

## Main statements

- `AddCommGroup.tateModule.eq_zero_of_pow_zsmul_eq_zero`: `T_ℓ M` has no `ℓ`-power torsion; it
  is a torsion-free `ℤ_[ℓ]`-module.
- `AddCommGroup.rationalTateModule.injective_one_tmul`: `T_ℓ M → V_ℓ M` is injective.
- `AddCommGroup.rationalTateModule.exists_eq_inv_pow_tmul`,
  `AddCommGroup.rationalTateModule.inv_pow_tmul_eq_inv_pow_tmul_iff`: `V_ℓ M = T_ℓ M [1 / ℓ]`.
- `AddCommGroup.tateModule.nonempty_linearEquiv_of_natCard_eq`,
  `AddCommGroup.rationalTateModule.nonempty_linearEquiv_of_natCard_eq`: if `M` is `ℓ`-divisible
  and `|M[ℓ]| = ℓ ^ r`, then `T_ℓ M ≅ ℤ_[ℓ] ^ r` and `V_ℓ M ≅ ℚ_[ℓ] ^ r`.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace AddCommGroup

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : Type u) [AddCommGroup M]

/-- Blueprint `definition-tate-module`: Integral and rational Tate modules.

The *Tate module* `T_ℓ M` of an abelian group `M` at a prime `ℓ` is the subgroup of the product
`∀ n : ℕ, M` consisting of the compatible systems `t` of `ℓ ^ n`-torsion points, that is, those
`t` with `ℓ ^ n • t n = 0` for all `n` and `ℓ • t (n + 1) = t n` for all `n`.

This is also blueprint `definition-tate-module`; the blueprint indexes from `n = 1`, and
the extra coordinate `t 0` here is always `0`. -/
def tateModule : AddSubgroup (∀ _ : ℕ, M) where
  carrier := {t | (∀ n, (ℓ : ℤ) ^ n • t n = 0) ∧ ∀ n, (ℓ : ℤ) • t (n + 1) = t n}
  zero_mem' := by simp
  add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ ↦
    ⟨fun n ↦ by simp [smul_add, ha n, hb n], fun n ↦ by simp [smul_add, ha' n, hb' n]⟩
  neg_mem' := fun ⟨ha, ha'⟩ ↦ ⟨fun n ↦ by simp [ha n], fun n ↦ by simp [ha' n]⟩

namespace tateModule

variable {ℓ M}

omit [Fact ℓ.Prime] in
theorem mem_iff {t : ∀ _ : ℕ, M} :
    t ∈ tateModule ℓ M ↔
      (∀ n, (ℓ : ℤ) ^ n • t n = 0) ∧ ∀ n, (ℓ : ℤ) • t (n + 1) = t n :=
  Iff.rfl

omit [Fact ℓ.Prime] in
/-- The `n`-th coordinate of an element of `T_ℓ M` is killed by `ℓ ^ n`. -/
theorem pow_zsmul_coe (t : tateModule ℓ M) (n : ℕ) :
    (ℓ : ℤ) ^ n • (t : ∀ _ : ℕ, M) n = 0 :=
  (mem_iff.mp t.2).1 n

omit [Fact ℓ.Prime] in
/-- The transition maps of `T_ℓ M` are multiplication by `ℓ`. -/
theorem zsmul_coe_succ (t : tateModule ℓ M) (n : ℕ) :
    (ℓ : ℤ) • (t : ∀ _ : ℕ, M) (n + 1) = (t : ∀ _ : ℕ, M) n :=
  (mem_iff.mp t.2).2 n

omit [Fact ℓ.Prime] in
/-- Two integers congruent modulo `ℓ ^ n` act in the same way on the `n`-th coordinate of an
element of the Tate module. -/
theorem zsmul_coe_congr {t : tateModule ℓ M} {n : ℕ} {x y : ℤ} (h : (ℓ : ℤ) ^ n ∣ x - y) :
    x • (t : ∀ _ : ℕ, M) n = y • (t : ∀ _ : ℕ, M) n := by
  obtain ⟨c, hc⟩ := h
  have hx : x = (ℓ : ℤ) ^ n * c + y := sub_eq_iff_eq_add.mp hc
  rw [hx, add_smul, mul_comm, mul_smul, pow_zsmul_coe, smul_zero, zero_add]

theorem natCast_appr (a : ℤ_[ℓ]) (n : ℕ) :
    ((a.appr n : ℕ) : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a :=
  rfl

omit [Fact ℓ.Prime] in
theorem dvd_sub_of_intCast_eq {n : ℕ} {x y : ℤ}
    (h : (x : ZMod (ℓ ^ n)) = (y : ZMod (ℓ ^ n))) : (ℓ : ℤ) ^ n ∣ x - y := by
  have h0 : ((x - y : ℤ) : ZMod (ℓ ^ n)) = 0 := by push_cast [h]; ring
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) (ℓ ^ n)).mp h0
  exact_mod_cast this

/-- An `ℓ`-adic integer acts on the `n`-th coordinate of the Tate module through any integer
representing it modulo `ℓ ^ n`. -/
theorem appr_zsmul_coe_eq (t : tateModule ℓ M) (a : ℤ_[ℓ]) {n : ℕ} {x : ℤ}
    (h : (x : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a) :
    (a.appr n : ℤ) • (t : ∀ _ : ℕ, M) n = x • (t : ∀ _ : ℕ, M) n :=
  zsmul_coe_congr (dvd_sub_of_intCast_eq (by rw [Int.cast_natCast, natCast_appr, h]))

/-- Blueprint `definition-tate-module`: Integral and rational Tate modules.

The Tate module `T_ℓ M` is a module over the ring `ℤ_[ℓ]` of `ℓ`-adic integers, acting
coordinatewise: an `ℓ`-adic integer acts on the `n`-th coordinate through its reduction modulo
`ℓ ^ n`. -/
noncomputable instance instSMul : SMul ℤ_[ℓ] (tateModule ℓ M) where
  smul a t := ⟨fun n ↦ (a.appr n : ℤ) • (t : ∀ _ : ℕ, M) n, by
    refine ⟨fun n ↦ ?_, fun n ↦ ?_⟩
    · dsimp only
      rw [smul_comm, pow_zsmul_coe, smul_zero]
    · dsimp only
      rw [smul_comm, zsmul_coe_succ]
      refine zsmul_coe_congr ?_
      obtain ⟨c, hc⟩ := PadicInt.dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n)
      refine ⟨c, ?_⟩
      have hsub : (a.appr (n + 1) : ℤ) - (a.appr n : ℤ) = ((a.appr (n + 1) - a.appr n : ℕ) : ℤ) :=
        (Nat.cast_sub (a.appr_mono (Nat.le_succ n))).symm
      rw [hsub, hc]
      push_cast
      ring⟩

theorem coe_smul_apply (a : ℤ_[ℓ]) (t : tateModule ℓ M) (n : ℕ) :
    ((a • t : tateModule ℓ M) : ∀ _ : ℕ, M) n = (a.appr n : ℤ) • (t : ∀ _ : ℕ, M) n :=
  rfl

noncomputable instance instModule : Module ℤ_[ℓ] (tateModule ℓ M) where
  one_smul t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, appr_zsmul_coe_eq t 1 (x := 1) (by rw [Int.cast_one, map_one]), one_smul]
  mul_smul a b t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, coe_smul_apply, coe_smul_apply,
      appr_zsmul_coe_eq t (a * b) (x := (a.appr n : ℤ) * (b.appr n : ℤ))
        (by push_cast [natCast_appr]; rw [map_mul]), mul_smul]
  smul_zero a := Subtype.ext <| funext fun n ↦ by simp [coe_smul_apply]
  smul_add a s t := Subtype.ext <| funext fun n ↦ by simp [coe_smul_apply, smul_add]
  add_smul a b t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, appr_zsmul_coe_eq t (a + b) (x := (a.appr n : ℤ) + (b.appr n : ℤ))
        (by push_cast [natCast_appr]; rw [map_add]), add_smul]
    simp [coe_smul_apply]
  zero_smul t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, appr_zsmul_coe_eq t 0 (x := 0) (by rw [Int.cast_zero, map_zero]), zero_smul]
    simp

omit [Fact ℓ.Prime] in
/-- The coordinates of an element of the Tate module are related by `ℓ ^ k • t (n + k) = t n`. -/
theorem pow_zsmul_coe_add (t : tateModule ℓ M) (n k : ℕ) :
    (ℓ : ℤ) ^ k • (t : ∀ _ : ℕ, M) (n + k) = (t : ∀ _ : ℕ, M) n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, smul_comm, ← add_assoc, zsmul_coe_succ, ih]

omit [Fact ℓ.Prime] in
/-- Part of blueprint `proposition-no-frobenius-fixed-vector`: the Tate module has no `ℓ`-power
torsion. -/
theorem eq_zero_of_pow_zsmul_eq_zero {t : tateModule ℓ M} {k : ℕ}
    (h : (ℓ : ℤ) ^ k • t = 0) : t = 0 :=
  Subtype.ext <| funext fun n ↦ by
    rw [← pow_zsmul_coe_add t n k]
    exact congr_fun (congr_arg Subtype.val h) (n + k)

/-- Part of blueprint `proposition-no-frobenius-fixed-vector`: the Tate module is a torsion-free
`ℤ_[ℓ]`-module, since a nonzero `ℓ`-adic integer is a unit times a power of `ℓ` and the Tate
module has no `ℓ`-power torsion. -/
instance : NoZeroSMulDivisors ℤ_[ℓ] (tateModule ℓ M) where
  eq_zero_or_eq_zero_of_smul_eq_zero {a t} h := by
    by_cases ha : a = 0
    · exact Or.inl ha
    refine Or.inr (eq_zero_of_pow_zsmul_eq_zero (k := a.valuation) ?_)
    have hspec := PadicInt.unitCoeff_spec ha
    set u := PadicInt.unitCoeff ha
    have h2 : (u : ℤ_[ℓ]) • ((ℓ : ℤ_[ℓ]) ^ a.valuation • t) = 0 := by rw [smul_smul, ← hspec, h]
    have h3 := congr_arg ((u⁻¹ : ℤ_[ℓ]ˣ) • ·) h2
    simp only [smul_zero, ← Units.smul_def, inv_smul_smul] at h3
    rw [← Int.cast_smul_eq_zsmul ℤ_[ℓ]]
    exact_mod_cast h3

variable {N : Type*} [AddCommGroup N]

/-- The map of Tate modules `T_ℓ M → T_ℓ N` induced by a homomorphism `M →+ N`, acting
coordinatewise. -/
noncomputable def map (f : M →+ N) : tateModule ℓ M →ₗ[ℤ_[ℓ]] tateModule ℓ N where
  toFun t := ⟨fun n ↦ f ((t : ∀ _ : ℕ, M) n), fun n ↦ by rw [← map_zsmul, pow_zsmul_coe, map_zero],
    fun n ↦ by rw [← map_zsmul, zsmul_coe_succ]⟩
  map_add' s t := Subtype.ext <| funext fun n ↦ by simp
  map_smul' a t := Subtype.ext <| funext fun n ↦ by simp [coe_smul_apply]

@[simp]
theorem coe_map_apply (f : M →+ N) (t : tateModule ℓ M) (n : ℕ) :
    ((map f t : tateModule ℓ N) : ∀ _ : ℕ, N) n = f ((t : ∀ _ : ℕ, M) n) :=
  rfl

/-- The isomorphism of Tate modules `T_ℓ M ≃ T_ℓ N` induced by an isomorphism `M ≃+ N`. -/
noncomputable def congr (e : M ≃+ N) : tateModule ℓ M ≃ₗ[ℤ_[ℓ]] tateModule ℓ N :=
  LinearEquiv.ofLinearMap (f := map e.toAddMonoidHom) (g := map e.symm.toAddMonoidHom)
    (LinearMap.ext fun _ ↦ Subtype.ext <| funext fun _ ↦ by simp)
    (LinearMap.ext fun _ ↦ Subtype.ext <| funext fun _ ↦ by simp)

variable (ℓ M) in
/-- Blueprint `proposition-integral-tate-module--2` (group-theoretic content): the Tate module of an
`ℓ`-divisible group is free.

Let `M` be an abelian group on which multiplication by the prime `ℓ` is surjective and whose
`ℓ`-torsion `M[ℓ]` has order `ℓ ^ r`. Then `T_ℓ M ≅ ℤ_[ℓ] ^ r`.

Choose an "integral basis" `e` of `M[ℓ]` (`AddSubgroup.exists_basis_torsionBy`) and compatible
lifts `z k` of `e` along multiplication by `ℓ ^ k`, so that `ℓ • z (k + 1) = z k`. The family
`z k` is a basis of `M[ℓ ^ (k + 1)]` over `ℤ / ℓ ^ (k + 1)`
(`AddSubgroup.sum_zsmul_dvd_and_exists_of_pow_zsmul_eq`); hence the elements
`(0, z 0 i, z 1 i, …)` of `T_ℓ M` form a `ℤ_[ℓ]`-basis of it: coordinates of an element of the
Tate module with respect to the `z k` form a compatible system modulo `ℓ ^ (k + 1)`, whose limit
is an `ℓ`-adic integer. -/
theorem nonempty_linearEquiv_of_natCard_eq (hdiv : ∀ x : M, ∃ y : M, (ℓ : ℤ) • y = x) (r : ℕ)
    (hr : Nat.card (AddSubgroup.torsionBy M (ℓ : ℤ)) = ℓ ^ r) :
    Nonempty (tateModule ℓ M ≃ₗ[ℤ_[ℓ]] (Fin r → ℤ_[ℓ])) := by
  obtain ⟨e, he₀, he, he'⟩ := AddSubgroup.exists_basis_torsionBy M ℓ r hr
  choose d hd using hdiv
  -- compatible lifts `z k` of `e` along multiplication by `ℓ ^ k`
  let z : ℕ → Fin r → M := fun k ↦ Nat.rec e (fun _ zk i ↦ d (zk i)) k
  have hz : ∀ k i, (ℓ : ℤ) • z (k + 1) i = z k i := fun k i ↦ hd _
  have hze : ∀ k i, (ℓ : ℤ) ^ k • z k i = e i := by
    intro k
    induction k with
    | zero => exact fun i ↦ one_smul ℤ _
    | succ k ih => intro i; rw [pow_succ, mul_smul, hz, ih]
  have hzk : ∀ k i, (ℓ : ℤ) ^ (k + 1) • z k i = 0 := fun k i ↦ by
    rw [pow_succ', mul_smul, hze, he₀]
  have key := fun k ↦
    AddSubgroup.sum_zsmul_dvd_and_exists_of_pow_zsmul_eq (ℓ : ℤ) e he he' k (z k) (hze k)
  -- the basis `b` of the Tate module
  let w : ℕ → Fin r → M := fun n i ↦ n.casesOn (0 : M) fun k ↦ z k i
  let b : Fin r → tateModule ℓ M := fun i ↦ ⟨fun n ↦ w n i, fun n ↦ by
      cases n with
      | zero => exact smul_zero _
      | succ k => exact hzk k i, fun n ↦ by
      cases n with
      | zero => exact he₀ i
      | succ k => exact hz k i⟩
  let φ := Fintype.linearCombination ℤ_[ℓ] b
  have hφ : ∀ a k, ((φ a : tateModule ℓ M) : ℕ → M) (k + 1) =
      ∑ i, ((a i).appr (k + 1) : ℤ) • z k i := fun a k ↦ by
    simp [φ, Fintype.linearCombination_apply, coe_smul_apply, b, w]
  -- an integer acts on `z k i` through its class modulo `ℓ ^ (k + 1)`
  have hcongr : ∀ k i {x y : ℤ}, (x : ZMod (ℓ ^ (k + 1))) = y → x • z k i = y • z k i := by
    intro k i x y h
    obtain ⟨m, hm⟩ := dvd_sub_of_intCast_eq h
    rw [sub_eq_iff_eq_add.mp hm, add_smul, mul_comm, mul_smul, hzk, smul_zero, zero_add]
  refine ⟨(LinearEquiv.ofBijective φ ⟨(injective_iff_map_eq_zero φ).2 fun a ha ↦ ?_, ?_⟩).symm⟩
  · refine funext fun i ↦ PadicInt.ext_of_toZModPow.1 fun n ↦ ?_
    cases n with
    | zero => exact Subsingleton.elim (α := ZMod 1) _ _
    | succ k =>
      have h := (key k).1 _ (by rw [← hφ, ha]; rfl) i
      rw [Pi.zero_apply, map_zero, ← natCast_appr, ← Int.cast_natCast]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by exact_mod_cast h)
  · intro t
    choose c hc using fun k ↦ (key k).2 _ (pow_zsmul_coe t (k + 1))
    have hcc : ∀ k i, (ℓ : ℤ) ^ (k + 1) ∣ c (k + 1) i - c k i := fun k ↦
      (key k).1 (fun i ↦ c (k + 1) i - c k i) <| by
        simp_rw [sub_smul, Finset.sum_sub_distrib]
        rw [sub_eq_zero, ← hc k, ← zsmul_coe_succ t (k + 1), hc (k + 1), Finset.smul_sum]
        simp_rw [smul_comm (ℓ : ℤ) (c _ _), hz]
    let f : Fin r → ℕ → ℤ := fun i n ↦ n.casesOn 0 fun k ↦ c k i
    have hf : ∀ i n, (ℓ : ℤ) ^ n ∣ f i (n + 1) - f i n := fun i n ↦ by
      cases n with
      | zero => rw [pow_zero]; exact one_dvd _
      | succ k => exact hcc k i
    refine ⟨fun i ↦ PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ ℓ (hf i)),
      Subtype.ext <| funext fun n ↦ ?_⟩
    cases n with
    | zero =>
      have h₁ := pow_zsmul_coe (φ fun i ↦ PadicInt.ofIntSeq _
        (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ ℓ (hf i))) 0
      have h₂ := pow_zsmul_coe t 0
      rw [pow_zero, one_smul] at h₁ h₂
      rw [h₁, h₂]
    | succ k =>
      rw [hφ, hc k]
      refine Finset.sum_congr rfl fun i _ ↦ hcongr k i ?_
      rw [Int.cast_natCast, natCast_appr, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ _ (hf i)]

end tateModule

/-- Blueprint `definition-tate-module`: Integral and rational Tate modules.

The *rational Tate module* `V_ℓ M = ℚ_[ℓ] ⊗_{ℤ_[ℓ]} T_ℓ M`. -/
def rationalTateModule : Type u :=
  ℚ_[ℓ] ⊗[ℤ_[ℓ]] (tateModule ℓ M)

namespace rationalTateModule

noncomputable instance : AddCommGroup (rationalTateModule ℓ M) :=
  inferInstanceAs (AddCommGroup (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (tateModule ℓ M)))

noncomputable instance : Module ℚ_[ℓ] (rationalTateModule ℓ M) :=
  inferInstanceAs (Module ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (tateModule ℓ M)))

/-- Part of blueprint `proposition-no-frobenius-fixed-vector`: since `T_ℓ M` is a torsion-free
`ℤ_[ℓ]`-module, the natural map `T_ℓ M → V_ℓ M = ℚ_[ℓ] ⊗ T_ℓ M`, `t ↦ 1 ⊗ t`, is injective. -/
theorem injective_one_tmul :
    Function.Injective fun t : tateModule ℓ M ↦ (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] t := by
  refine (injective_iff_map_eq_zero (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (tateModule ℓ M) 1)).mpr
    fun t ht ↦ ?_
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) _).mp ht
  exact (smul_eq_zero.mp hc).resolve_left (nonZeroDivisors.ne_zero c.2)

variable {ℓ M} in
/-- Blueprint `definition-tate-module`: rescaling a fraction. The fraction `ℓ ^ (-b) t`
equals `ℓ ^ (-(b + c)) (ℓ ^ c t)` in `V_ℓ M`. -/
theorem inv_pow_tmul_eq_inv_pow_add_tmul (b c : ℕ) (t : tateModule ℓ M) :
    ((ℓ : ℚ_[ℓ]) ^ b)⁻¹ ⊗ₜ[ℤ_[ℓ]] t =
      ((ℓ : ℚ_[ℓ]) ^ (b + c))⁻¹ ⊗ₜ[ℤ_[ℓ]] ((ℓ : ℤ_[ℓ]) ^ c • t) := by
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, PadicInt.algebraMap_apply,
    PadicInt.coe_pow, PadicInt.coe_natCast]
  congr 1
  have hℓ : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  field_simp
  ring

variable {ℓ M} in
/-- Blueprint `definition-tate-module`: Tate module of an abelian group.

`V_ℓ M = T_ℓ M [1 / ℓ]`: every element of the rational Tate module is a fraction `ℓ ^ (-b) t`
with `t ∈ T_ℓ M`. -/
theorem exists_eq_inv_pow_tmul (v : ℚ_[ℓ] ⊗[ℤ_[ℓ]] tateModule ℓ M) :
    ∃ (b : ℕ) (t : tateModule ℓ M), v = ((ℓ : ℚ_[ℓ]) ^ b)⁻¹ ⊗ₜ[ℤ_[ℓ]] t := by
  induction v using TensorProduct.inductionOn with
  | tmul q t =>
    obtain ⟨b, z, rfl⟩ := Padic.exists_eq_inv_pow_mul q
    refine ⟨b, z • t, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, PadicInt.algebraMap_apply, mul_comm]
  | add v w hv hw =>
    obtain ⟨b, t, rfl⟩ := hv
    obtain ⟨c, u, rfl⟩ := hw
    refine ⟨b + c, (ℓ : ℤ_[ℓ]) ^ c • t + (ℓ : ℤ_[ℓ]) ^ b • u, ?_⟩
    rw [TensorProduct.tmul_add, inv_pow_tmul_eq_inv_pow_add_tmul b c,
      inv_pow_tmul_eq_inv_pow_add_tmul c b, add_comm c b]

variable {ℓ M} in
/-- Blueprint `definition-tate-module`: Tate module of an abelian group.

Equality of fractions in `V_ℓ M = T_ℓ M [1 / ℓ]`: `ℓ ^ (-b) t = ℓ ^ (-c) u` if and only if
`ℓ ^ d (ℓ ^ c t - ℓ ^ b u) = 0` for some `d ≥ 0`. -/
theorem inv_pow_tmul_eq_inv_pow_tmul_iff (b c : ℕ) (t u : tateModule ℓ M) :
    ((ℓ : ℚ_[ℓ]) ^ b)⁻¹ ⊗ₜ[ℤ_[ℓ]] t = ((ℓ : ℚ_[ℓ]) ^ c)⁻¹ ⊗ₜ[ℤ_[ℓ]] u ↔
      ∃ d : ℕ, (ℓ : ℤ) ^ d • ((ℓ : ℤ) ^ c • t - (ℓ : ℤ) ^ b • u) = 0 := by
  have hcast (k : ℕ) (s : tateModule ℓ M) : (ℓ : ℤ) ^ k • s = (ℓ : ℤ_[ℓ]) ^ k • s := by
    rw [← Int.cast_smul_eq_zsmul ℤ_[ℓ]]
    push_cast
    rfl
  rw [inv_pow_tmul_eq_inv_pow_add_tmul b c, inv_pow_tmul_eq_inv_pow_add_tmul c b, add_comm c b]
  constructor
  · intro h
    refine ⟨0, ?_⟩
    have h' := congrArg (((ℓ : ℚ_[ℓ]) ^ (b + c)) • ·) h
    have hℓ : ((ℓ : ℚ_[ℓ]) ^ (b + c)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne ℓ))
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_inv_cancel₀ hℓ] at h'
    rw [pow_zero, one_smul, hcast, hcast, sub_eq_zero]
    exact injective_one_tmul ℓ M h'
  · rintro ⟨d, h⟩
    have h0 := tateModule.eq_zero_of_pow_zsmul_eq_zero h
    rw [sub_eq_zero, hcast, hcast] at h0
    rw [h0]


variable {ℓ M} {N : Type*} [AddCommGroup N]

/-- The map of rational Tate modules `V_ℓ M → V_ℓ N` induced by a homomorphism `M →+ N`. -/
noncomputable def map (f : M →+ N) : rationalTateModule ℓ M →ₗ[ℚ_[ℓ]] rationalTateModule ℓ N :=
  (tateModule.map f).baseChange ℚ_[ℓ]

theorem map_tmul (f : M →+ N) (a : ℚ_[ℓ]) (t : tateModule ℓ M) :
    map f (a ⊗ₜ[ℤ_[ℓ]] t : ℚ_[ℓ] ⊗[ℤ_[ℓ]] tateModule ℓ M) =
      (a ⊗ₜ[ℤ_[ℓ]] tateModule.map f t : ℚ_[ℓ] ⊗[ℤ_[ℓ]] tateModule ℓ N) :=
  rfl

variable (ℓ) in
/-- Blueprint `definition-tate-module`: Tate module of an abelian group.

The fixed submodule `(V_ℓ M)^s` of an endomorphism `s` of `M` (in the blueprint an
automorphism), which acts on `V_ℓ M` coordinatewise and on fractions through
`AddCommGroup.rationalTateModule.map`. -/
noncomputable def fixedSubmodule (s : M →+ M) : Submodule ℚ_[ℓ] (rationalTateModule ℓ M) :=
  LinearMap.eqLocus (map s) LinearMap.id

theorem mem_fixedSubmodule {s : M →+ M} {v : rationalTateModule ℓ M} :
    v ∈ fixedSubmodule ℓ s ↔ map s v = v :=
  Iff.rfl


variable (ℓ M) in
/-- Blueprint `proposition-integral-tate-module--2` (group-theoretic content, rational form): if
multiplication by the prime `ℓ` is surjective on `M` and `M[ℓ]` has order `ℓ ^ r`, then
`V_ℓ M ≅ ℚ_[ℓ] ^ r`. This is the base change to `ℚ_[ℓ]` of
`AddCommGroup.tateModule.nonempty_linearEquiv_of_natCard_eq`. -/
theorem nonempty_linearEquiv_of_natCard_eq (hdiv : ∀ x : M, ∃ y : M, (ℓ : ℤ) • y = x) (r : ℕ)
    (hr : Nat.card (AddSubgroup.torsionBy M (ℓ : ℤ)) = ℓ ^ r) :
    Nonempty (rationalTateModule ℓ M ≃ₗ[ℚ_[ℓ]] (Fin r → ℚ_[ℓ])) :=
  let ⟨e⟩ := tateModule.nonempty_linearEquiv_of_natCard_eq ℓ M hdiv r hr
  ⟨(e.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _).trans (TensorProduct.piScalarRight ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ] (Fin r))⟩

end rationalTateModule

end AddCommGroup
