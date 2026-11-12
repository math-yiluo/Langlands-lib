import Mathlib

/-! # Extending derivations to adic completions -/

namespace Langlands.CommutativeAlgebra.FiniteTypeIntGRing

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (D : R →+ R) (hD : ∀ a b, D (a * b) = a * D b + b * D a)

include hD in
/-- A map satisfying the Leibniz rule sends `I ^ (n + 1)` into `I ^ n`. -/
theorem leibniz_mem_pow_of_mem_pow_succ (n : ℕ) {x : R} (hx : x ∈ I ^ (n + 1)) :
    D x ∈ I ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [hD, pow_succ]
      refine add_mem (Ideal.mul_mem_right _ _ (pow_succ I n ▸ ha)) ?_
      rw [mul_comm b]
      exact Ideal.mul_mem_mul (ih ha) hb
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy

private theorem mem_smul_top_iff (n : ℕ) (y : R) : y ∈ (I ^ n • ⊤ : Ideal R) ↔ y ∈ I ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

/-- The `n`-th component of the extended derivation: apply `D` to a lift of the
`(n + 1)`-st component. -/
noncomputable def completionDerivAux (x : AdicCompletion I R) (n : ℕ) :
    R ⧸ (I ^ n • ⊤ : Ideal R) :=
  Ideal.Quotient.mk _ (D (Quotient.out (x.val (n + 1))))

include hD in
theorem completionDerivAux_eq (x : AdicCompletion I R) (n : ℕ) (a : R)
    (ha : Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) a = x.val (n + 1)) :
    completionDerivAux I D x n = Ideal.Quotient.mk _ (D a) := by
  unfold completionDerivAux
  rw [Ideal.Quotient.eq, ← map_sub]
  have h1 : Quotient.out (x.val (n + 1)) - a ∈ (I ^ (n + 1) • ⊤ : Ideal R) := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out, ha]
  exact (mem_smul_top_iff I n _).mpr
    (leibniz_mem_pow_of_mem_pow_succ I D hD n ((mem_smul_top_iff I (n + 1) _).mp h1))

private theorem val_eq_mk (x : AdicCompletion I R) {m n : ℕ} (hmn : m ≤ n) (a : R)
    (ha : Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) a = x.val n) :
    Ideal.Quotient.mk (I ^ m • ⊤ : Ideal R) a = x.val m := by
  rw [← x.prop hmn, ← ha]
  rfl

/-- The extension of a Leibniz map `D : R → R` to the `I`-adic completion. -/
noncomputable def completionDeriv : AdicCompletion I R →+ AdicCompletion I R where
  toFun x := ⟨completionDerivAux I D x, fun {m n} hmn => by
    rw [completionDerivAux_eq I D hD x m (Quotient.out (x.val (n + 1)))
      (val_eq_mk I x (by omega) _ (Ideal.Quotient.mk_out _))]
    rfl⟩
  map_zero' := by
    ext n
    change completionDerivAux I D 0 n = 0
    rw [completionDerivAux_eq I D hD 0 n 0 (by simp), map_zero, map_zero]
  map_add' x y := by
    ext n
    change completionDerivAux I D (x + y) n =
      completionDerivAux I D x n + completionDerivAux I D y n
    rw [completionDerivAux_eq I D hD (x + y) n
      (Quotient.out (x.val (n + 1)) + Quotient.out (y.val (n + 1))) (by
        rw [map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out]; rfl),
      map_add, map_add]
    rfl

theorem completionDeriv_val (x : AdicCompletion I R) (n : ℕ) (a : R)
    (ha : Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) a = x.val (n + 1)) :
    (completionDeriv I D hD x).val n = Ideal.Quotient.mk _ (D a) :=
  completionDerivAux_eq I D hD x n a ha

theorem completionDeriv_of (a : R) :
    completionDeriv I D hD (AdicCompletion.of I R a) = AdicCompletion.of I R (D a) := by
  ext n
  rw [completionDeriv_val I D hD _ n a rfl]
  rfl

theorem completionDeriv_mul (x y : AdicCompletion I R) :
    completionDeriv I D hD (x * y) =
      x * completionDeriv I D hD y + y * completionDeriv I D hD x := by
  ext n
  set a := Quotient.out (x.val (n + 1))
  set b := Quotient.out (y.val (n + 1))
  have ha : Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) a = x.val (n + 1) :=
    Ideal.Quotient.mk_out _
  have hb : Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) b = y.val (n + 1) :=
    Ideal.Quotient.mk_out _
  rw [AdicCompletion.val_add_apply, AdicCompletion.val_mul, AdicCompletion.val_mul,
    completionDeriv_val I D hD (x * y) n (a * b)
      (by rw [map_mul, ha, hb, AdicCompletion.val_mul]),
    completionDeriv_val I D hD y n b hb, completionDeriv_val I D hD x n a ha,
    ← val_eq_mk I x (Nat.le_succ n) a ha, ← val_eq_mk I y (Nat.le_succ n) b hb, hD]
  simp only [map_add, map_mul]

end Langlands.CommutativeAlgebra.FiniteTypeIntGRing
