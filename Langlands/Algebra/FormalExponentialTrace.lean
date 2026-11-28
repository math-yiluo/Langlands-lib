import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Logarithmic derivatives of formal exponentials under a cyclic trace -/

noncomputable section

namespace Langlands.FormalPowerSeries

open PowerSeries Finset
open scoped PowerSeries

section Filtration

variable {R : Type*} [Ring R]

/-- A formal series whose coefficients below `n` vanish. -/
def VanishesBelow (n : ℕ) (f : PowerSeries R) : Prop := ∀ m < n, coeff m f = 0

theorem vanishesBelow_zero (f : PowerSeries R) : VanishesBelow 0 f := fun _ h => (Nat.not_lt_zero _ h).elim

theorem VanishesBelow.mul {f g : PowerSeries R} {i j : ℕ}
    (hf : VanishesBelow i f) (hg : VanishesBelow j g) : VanishesBelow (i + j) (f * g) := by
  intro n hn
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hsum := Finset.mem_antidiagonal.mp hp
  by_cases h : p.1 < i
  · rw [hf _ h, zero_mul]
  · rw [hg _ (by omega), mul_zero]

theorem VanishesBelow.pow {f : PowerSeries R} (hf : VanishesBelow 1 f) (k : ℕ) :
    VanishesBelow k (f ^ k) := by
  induction k with
  | zero => exact vanishesBelow_zero _
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem VanishesBelow.mul_right {f : PowerSeries R} {n : ℕ} (hf : VanishesBelow n f)
    (g : PowerSeries R) : VanishesBelow n (f * g) := by
  simpa only [add_zero] using hf.mul (vanishesBelow_zero g)

theorem VanishesBelow.mul_left {g : PowerSeries R} {n : ℕ} (hg : VanishesBelow n g) (f : PowerSeries R) :
    VanishesBelow n (f * g) := by
  simpa only [zero_add] using (vanishesBelow_zero f).mul hg

theorem VanishesBelow.inv_sub_inv {u v : (PowerSeries R)ˣ} {n : ℕ}
    (h : VanishesBelow n ((u : PowerSeries R) - (v : PowerSeries R))) :
    VanishesBelow n ((↑u⁻¹ : PowerSeries R) - (↑v⁻¹ : PowerSeries R)) := by
  have h' : VanishesBelow n ((v : PowerSeries R) - (u : PowerSeries R)) := fun k hk => by
    rw [← neg_sub, map_neg, h k hk, neg_zero]
  have hEq : (↑u⁻¹ : PowerSeries R) * ((v : PowerSeries R) - (u : PowerSeries R)) * ↑v⁻¹ =
      (↑u⁻¹ : PowerSeries R) - (↑v⁻¹ : PowerSeries R) := by
    rw [mul_sub, sub_mul, mul_assoc (↑u⁻¹ : PowerSeries R) (↑v : PowerSeries R),
      Units.mul_inv, mul_one, Units.inv_mul, one_mul]
  rw [← hEq]
  exact (h'.mul_left _).mul_right _

theorem VanishesBelow.coeff_mul {f g : PowerSeries R} {n : ℕ} (hf : VanishesBelow n f) :
    coeff n (f * g) = coeff n f * coeff 0 g := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (n, 0)]
  · intro p hp hne
    have hsum := Finset.mem_antidiagonal.mp hp
    have hlt : p.1 < n := by
      by_contra! h
      apply hne
      exact Prod.ext (by omega) (by omega)
    rw [hf _ hlt, zero_mul]
  · intro hn
    exact (hn (Finset.mem_antidiagonal.mpr (add_zero _))).elim

/-- The unit of a formal series with constant coefficient one. -/
def unitOfConstantOne (f : PowerSeries R) (hf : constantCoeff f = 1) : (PowerSeries R)ˣ :=
  ⟨f, invOfUnit f 1, mul_invOfUnit f 1 hf, invOfUnit_mul f 1 hf⟩

end Filtration

section Euler

variable {F R : Type*} [CommSemiring F] [Ring R] [Algebra F R]

/-- The Euler derivative `t · d/dt` of a formal series with associative coefficients. -/
def euler : PowerSeries R →ₗ[F] PowerSeries R where
  toFun f := PowerSeries.mk fun n => n • coeff n f
  map_add' f g := by
    ext n
    simp only [coeff_mk, map_add, nsmul_add]
  map_smul' c f := by
    ext n
    simp only [RingHom.id_apply, coeff_mk, coeff_smul, smul_comm c n]

@[simp] theorem coeff_euler (n : ℕ) (f : PowerSeries R) : coeff n (euler (F := F) f) = n • coeff n f := by
  change coeff n (PowerSeries.mk (fun k => k • coeff k f)) = _
  exact coeff_mk n _

/-- The Euler derivative satisfies the product rule for noncommuting coefficients. -/
theorem euler_mul (f g : PowerSeries R) : euler (F := F) (f * g) = euler (F := F) f * g + f * euler (F := F) g := by
  ext n
  rw [coeff_euler, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have h := Finset.mem_antidiagonal.mp hp
  rw [coeff_euler, coeff_euler, smul_mul_assoc, mul_smul_comm, ← add_nsmul, h]

@[simp] theorem euler_one : euler (F := F) (1 : PowerSeries R) = 0 := by
  ext n
  cases n <;> simp

theorem VanishesBelow.euler {n : ℕ} {f : PowerSeries R} (hf : VanishesBelow n f) :
    VanishesBelow n (euler (F := F) f) := fun m hm => by simp [hf m hm]

theorem euler_vanishesBelow_one (f : PowerSeries R) : VanishesBelow 1 (euler (F := F) f) := by
  intro n hn
  have : n = 0 := by omega
  subst n
  simp

end Euler

section Trace

variable {F R M : Type*} [CommSemiring F] [Ring R] [Algebra F R] [AddCommGroup M] [Module F M]
  (τ : R →ₗ[F] M)

/-- Apply a linear trace coefficientwise. -/
def seriesTrace : PowerSeries R →ₗ[F] ℕ → M where
  toFun f n := τ (coeff n f)
  map_add' f g := by funext n; simp
  map_smul' c f := by funext n; simp

@[simp] theorem seriesTrace_apply (f : PowerSeries R) (n : ℕ) : seriesTrace τ f n = τ (coeff n f) := rfl

variable (hτ : ∀ x y : R, τ (x * y) = τ (y * x))

include hτ in
theorem seriesTrace_mul_comm (f g : PowerSeries R) : seriesTrace τ (f * g) = seriesTrace τ (g * f) := by
  funext n
  simp only [seriesTrace_apply, coeff_mul, map_sum]
  simp_rw [hτ (coeff _ f)]
  exact Finset.Nat.sum_antidiagonal_swap (f := fun p => τ (coeff p.1 g * coeff p.2 f))

/-- The right logarithmic derivative of a unit series. -/
def logarithmicEuler (u : (PowerSeries R)ˣ) : PowerSeries R := euler (F := F) (u : PowerSeries R) * ↑u⁻¹

include hτ in
theorem seriesTrace_logarithmicEuler_mul (u v : (PowerSeries R)ˣ) :
    seriesTrace τ (logarithmicEuler (F := F) (u * v)) =
      seriesTrace τ (logarithmicEuler (F := F) u) + seriesTrace τ (logarithmicEuler (F := F) v) := by
  rw [show logarithmicEuler (F := F) (u * v) = logarithmicEuler (F := F) u +
      (u : PowerSeries R) * logarithmicEuler (F := F) v * (↑u⁻¹ : PowerSeries R) by
    simp only [logarithmicEuler, Units.val_mul, mul_inv_rev, euler_mul, add_mul, mul_assoc,
      Units.mul_inv_cancel_left]]
  rw [map_add, seriesTrace_mul_comm τ hτ _ (↑u⁻¹ : PowerSeries R), ← mul_assoc, Units.inv_mul, one_mul]

include hτ in
theorem seriesTrace_conjugate (u : (PowerSeries R)ˣ) (f : PowerSeries R) :
    seriesTrace τ ((u : PowerSeries R) * f * ↑u⁻¹) = seriesTrace τ f := by
  rw [seriesTrace_mul_comm τ hτ _ (↑u⁻¹ : PowerSeries R), ← mul_assoc, Units.inv_mul, one_mul]

include hτ in
private theorem seriesTrace_euler_pow (f g : PowerSeries R) (hfg : Commute f g) (k : ℕ) :
    seriesTrace τ (euler (F := F) (f ^ (k + 1)) * g) =
      (k + 1) • seriesTrace τ (euler (F := F) f * (f ^ k * g)) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [pow_succ f (k + 1), euler_mul, add_mul, map_add, mul_assoc (euler (F := F) (f ^ (k + 1))),
      ih (f * g) ((Commute.refl f).mul_right hfg)]
    have hc : seriesTrace τ (f ^ (k + 1) * euler (F := F) f * g) =
        seriesTrace τ (euler (F := F) f * (f ^ (k + 1) * g)) := by
      rw [mul_assoc, seriesTrace_mul_comm τ hτ (f ^ (k + 1)), mul_assoc (euler (F := F) f),
        (hfg.pow_left (k + 1)).eq.symm]
    rw [hc, ← mul_assoc (f ^ k) f g, ← pow_succ]
    exact (succ_nsmul _ _).symm

end Trace

section Exponential

variable (F : Type*) [Field F] {R : Type*} [Ring R] [Algebra F R]

/-- The finite factorial sum through exponent `N`. -/
def exponentialPartial (N : ℕ) (f : PowerSeries R) : PowerSeries R :=
  ∑ k ∈ Finset.range (N + 1), ((k.factorial : F)⁻¹) • f ^ k

/-- The formal exponential, evaluated coefficientwise on a series with constant term zero. -/
def formalExponential (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => coeff n (exponentialPartial F n f)

theorem coeff_formalExponential_of_le {f : PowerSeries R} (hf : VanishesBelow 1 f) {n N : ℕ} (hn : n ≤ N) :
    coeff n (formalExponential F f) = coeff n (exponentialPartial F N f) := by
  simp only [formalExponential, coeff_mk, exponentialPartial, map_sum, coeff_smul]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))
  intro k _ hk
  have hkn : n < k := by simpa only [Finset.mem_range, Nat.lt_succ_iff, not_le] using hk
  rw [hf.pow k n hkn, smul_zero]

@[simp] theorem constantCoeff_formalExponential (f : PowerSeries R) : constantCoeff (formalExponential F f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, formalExponential, coeff_mk, exponentialPartial]
  simp

/-- The formal exponential as a unit series, with inverse given by inversion of a series
with constant coefficient one. -/
def exponentialUnit (f : PowerSeries R) : (PowerSeries R)ˣ :=
  unitOfConstantOne (formalExponential F f) (constantCoeff_formalExponential F f)

private theorem commute_formalExponential {f : PowerSeries R} (hf : VanishesBelow 1 f) :
    Commute f (formalExponential F f) := by
  ext n
  have h (k : ℕ) (hk : k ≤ n) := coeff_formalExponential_of_le F hf hk
  have hComm : Commute f (exponentialPartial F n f) := by
    unfold exponentialPartial
    apply Commute.sum_right
    intro k _
    exact ((Commute.refl f).pow_right k).smul_right _
  have h₀ := congrArg (coeff n) hComm.eq
  simp only [coeff_mul] at *
  calc
    _ = ∑ p ∈ Finset.antidiagonal n, coeff p.1 f * coeff p.2 (exponentialPartial F n f) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.mem_antidiagonal.mp hp
      rw [h _ (by omega)]
    _ = _ := h₀.trans (by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.mem_antidiagonal.mp hp
      rw [h _ (by omega)])

variable {M : Type*} [AddCommGroup M] [Module F M] (τ : R →ₗ[F] M)
  (hτ : ∀ x y : R, τ (x * y) = τ (y * x))

/-- Under a cyclic trace, the right logarithmic Euler derivative of a formal
exponential equals the Euler derivative of its exponent. -/
def FormalExponentialTraceStatement (F : Type*) [Field F] [CharZero F] {R : Type*}
    [Ring R] [Algebra F R] {M : Type*} [AddCommGroup M] [Module F M] (τ : R →ₗ[F] M) : Prop :=
  (∀ x y : R, τ (x * y) = τ (y * x)) → ∀ f : PowerSeries R, VanishesBelow 1 f →
    seriesTrace τ (logarithmicEuler (F := F) (exponentialUnit F f)) = seriesTrace τ (euler (F := F) f)

variable [CharZero F]

/-- If two unit series with constant term one agree in degrees below `n > 0`, and
have the same logarithmic derivative under a cyclic trace, their degree `n` difference
has zero trace. -/
theorem trace_coeff_sub_eq_zero_of_logarithmicEuler
    (u v : (PowerSeries R)ˣ) (hu : constantCoeff (u : PowerSeries R) = 1) {n : ℕ}
    (hn : 0 < n) (hBelow : VanishesBelow n ((u : PowerSeries R) - (v : PowerSeries R)))
    (hTr : seriesTrace τ (logarithmicEuler (F := F) u) = seriesTrace τ (logarithmicEuler (F := F) v)) :
    τ (coeff n ((u : PowerSeries R) - (v : PowerSeries R))) = 0 := by
  have hInv : coeff 0 (↑u⁻¹ : PowerSeries R) = 1 := by
    have h : constantCoeff ((u : PowerSeries R) * (↑u⁻¹ : PowerSeries R)) = 1 := by
      rw [Units.mul_inv, map_one]
    rw [map_mul, hu, one_mul] at h
    rwa [coeff_zero_eq_constantCoeff_apply]
  have hMixed := ((euler_vanishesBelow_one (F := F) (v : PowerSeries R)).mul hBelow.inv_sub_inv) n (by omega)
  have hDiff : logarithmicEuler (F := F) u - logarithmicEuler (F := F) v =
      euler (F := F) ((u : PowerSeries R) - (v : PowerSeries R)) * ↑u⁻¹ +
        euler (F := F) (v : PowerSeries R) * ((↑u⁻¹ : PowerSeries R) - (↑v⁻¹ : PowerSeries R)) := by
    simp only [logarithmicEuler, map_sub, sub_mul, mul_sub]
    abel
  have hCoeff : coeff n (logarithmicEuler (F := F) u - logarithmicEuler (F := F) v) =
      n • coeff n ((u : PowerSeries R) - (v : PowerSeries R)) := by
    rw [hDiff, map_add, hMixed, add_zero, (hBelow.euler (F := F)).coeff_mul, hInv, mul_one, coeff_euler]
  have h : n • τ (coeff n ((u : PowerSeries R) - (v : PowerSeries R))) = 0 := by
    rw [← map_nsmul, ← hCoeff, map_sub, map_sub, ← seriesTrace_apply, ← seriesTrace_apply, hTr, sub_self]
  rw [← Nat.cast_smul_eq_nsmul F, smul_eq_zero] at h
  exact h.resolve_left (Nat.cast_ne_zero.mpr hn.ne')

set_option maxHeartbeats 2500000 in
theorem formalExponentialTrace : FormalExponentialTraceStatement F τ := by
  intro hτ f hf
  let u := exponentialUnit F f
  let g : PowerSeries R := ↑u⁻¹
  have hfu : Commute f (u : PowerSeries R) := commute_formalExponential F hf
  have hfg : Commute f g := hfu.units_inv_right
  funext n
  let N := n + 1
  have hApprox : VanishesBelow (n + 1) ((u : PowerSeries R) - exponentialPartial F N f) := by
    intro m hm
    exact sub_eq_zero.mpr (coeff_formalExponential_of_le F hf (by omega))
  have hApproxEuler := (hApprox.euler (F := F)).mul_right g
  have hApproxExp := (hApprox.mul_left (euler (F := F) f)).mul_right g
  have h₁ : coeff n (euler (F := F) (u : PowerSeries R) * g) =
      coeff n (euler (F := F) (exponentialPartial F N f) * g) := by
    have h := hApproxEuler n (Nat.lt_succ_self n)
    simpa only [map_sub, sub_mul, sub_eq_zero] using h
  have h₂ : coeff n (euler (F := F) f * (u : PowerSeries R) * g) =
      coeff n (euler (F := F) f * exponentialPartial F N f * g) := by
    have h := hApproxExp n (Nat.lt_succ_self n)
    simpa only [map_sub, mul_sub, sub_mul, sub_eq_zero] using h
  have hExpand : seriesTrace τ (euler (F := F) (exponentialPartial F N f) * g) =
      seriesTrace τ (euler (F := F) f * exponentialPartial F (N - 1) f * g) := by
    unfold exponentialPartial
    rw [Finset.sum_range_succ', map_add, pow_zero, map_smul, euler_one, smul_zero, add_zero]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, map_smul, smul_mul_assoc, mul_smul_comm]
    rw [show N - 1 + 1 = N by rfl]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [seriesTrace_euler_pow τ hτ f g hfg k, ← mul_assoc]
    rw [← Nat.cast_smul_eq_nsmul F, smul_smul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
    have hk : ((k + 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    rw [mul_assoc, inv_mul_cancel₀ hk, mul_one]
  have hLast : coeff n (euler (F := F) f * exponentialPartial F N f * g) =
      coeff n (euler (F := F) f * exponentialPartial F (N - 1) f * g) := by
    have hPow : VanishesBelow N (((N.factorial : F)⁻¹) • f ^ N) := fun m hm => by
      rw [coeff_smul, hf.pow _ _ hm, smul_zero]
    have hZero := ((euler_vanishesBelow_one (F := F) f).mul hPow).mul_right g n (by omega)
    rw [show exponentialPartial F N f = exponentialPartial F (N - 1) f +
      ((N.factorial : F)⁻¹) • f ^ N by
      unfold exponentialPartial
      rw [Finset.sum_range_succ, show N - 1 + 1 = N by rfl]]
    rw [mul_add, add_mul, map_add, hZero, add_zero]
  change τ (coeff n (euler (F := F) (u : PowerSeries R) * g)) = τ (coeff n (euler (F := F) f))
  rw [h₁]
  exact (congrFun hExpand n).trans (by
    change τ (coeff n (euler (F := F) f * exponentialPartial F (N - 1) f * g)) = _
    rw [← hLast, ← h₂, mul_assoc, show (u : PowerSeries R) * g = 1 from Units.mul_inv u, mul_one])

end Exponential

end Langlands.FormalPowerSeries
