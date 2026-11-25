/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Additive maps between `ℤ_p`-modules killed by `pᵐ` are `ℤ_p`-linear

On a `ℤ_p`-module killed by `pᵐ`, the scalar `r ∈ ℤ_p` acts as the natural number
`PadicInt.appr r m`, which is congruent to `r` modulo `pᵐ`
(`PadicInt.smul_eq_appr_nsmul`). Hence every additive map between two such modules is
`ℤ_p`-linear (`PadicInt.linearMapOfPowSMulEqZero`), and every biadditive map is `ℤ_p`-bilinear
(`PadicInt.bilinearOfPowSMulEqZero`).
-/

@[expose] public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {M N P : Type*} [AddCommGroup M] [Module ℤ_[p] M]
  [AddCommGroup N] [Module ℤ_[p] N] [AddCommGroup P] [Module ℤ_[p] P]

/-- On a module killed by `pᵐ`, `r` acts as the natural number `appr r m`. -/
lemma smul_eq_appr_nsmul (hM : ∀ y : M, (p : ℤ_[p]) ^ m • y = 0) (r : ℤ_[p]) (y : M) :
    r • y = r.appr m • y := by
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (r.appr_spec m)
  conv_lhs => rw [← sub_add_cancel r (r.appr m : ℤ_[p]), ← hs]
  rw [add_smul, mul_comm, mul_smul, hM,
    zero_add, Nat.cast_smul_eq_nsmul]

/-- An additive map between `ℤ_p`-modules killed by `pᵐ` is `ℤ_p`-linear. -/
noncomputable def linearMapOfPowSMulEqZero (hM : ∀ y : M, (p : ℤ_[p]) ^ m • y = 0)
    (hN : ∀ y : N, (p : ℤ_[p]) ^ m • y = 0) (f : M →+ N) : M →ₗ[ℤ_[p]] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r y := by
    rw [smul_eq_appr_nsmul hM, map_nsmul, RingHom.id_apply, smul_eq_appr_nsmul hN]

@[simp]
lemma linearMapOfPowSMulEqZero_apply (hM : ∀ y : M, (p : ℤ_[p]) ^ m • y = 0)
    (hN : ∀ y : N, (p : ℤ_[p]) ^ m • y = 0) (f : M →+ N) (y : M) :
    linearMapOfPowSMulEqZero hM hN f y = f y :=
  rfl

/-- A biadditive map between `ℤ_p`-modules killed by `pᵐ` is `ℤ_p`-bilinear. -/
noncomputable def bilinearOfPowSMulEqZero (hM : ∀ y : M, (p : ℤ_[p]) ^ m • y = 0)
    (hN : ∀ y : N, (p : ℤ_[p]) ^ m • y = 0) (hP : ∀ y : P, (p : ℤ_[p]) ^ m • y = 0)
    (f : M →+ N →+ P) : M →ₗ[ℤ_[p]] N →ₗ[ℤ_[p]] P :=
  LinearMap.mk₂ ℤ_[p] (fun x y ↦ f x y) (fun x x' y ↦ by simp) (fun r x y ↦ by
      rw [smul_eq_appr_nsmul hM, map_nsmul, AddMonoidHom.nsmul_apply, smul_eq_appr_nsmul hP])
    (fun x y y' ↦ map_add _ _ _) fun r x y ↦ by
      rw [smul_eq_appr_nsmul hN, map_nsmul, smul_eq_appr_nsmul hP]

@[simp]
lemma bilinearOfPowSMulEqZero_apply (hM : ∀ y : M, (p : ℤ_[p]) ^ m • y = 0)
    (hN : ∀ y : N, (p : ℤ_[p]) ^ m • y = 0) (hP : ∀ y : P, (p : ℤ_[p]) ^ m • y = 0)
    (f : M →+ N →+ P) (x : M) (y : N) :
    bilinearOfPowSMulEqZero hM hN hP f x y = f x y :=
  rfl

/-- `ℤ_p / pᵐ` is killed by `pᵐ`. -/
lemma pow_smul_quotient_eq_zero (y : ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m}) :
    (p : ℤ_[p]) ^ m • y = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | H r =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- `ℤ_p / pᵐ` is `ℤ/pᵐ`. -/
noncomputable def quotientSpanPowRingEquiv (m : ℕ) :
    ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m} ≃+* ZMod (p ^ m) :=
  (Ideal.quotEquivOfEq (ker_toZModPow m).symm).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (toZModPow m)))

end PadicInt
