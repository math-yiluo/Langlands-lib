import Langlands.Algebra.BoundedWordSeries
import Mathlib.Tactic.NoncommRing

/-! # Degree-by-degree straightening in the formal word algebra -/

noncomputable section

namespace Langlands.CyclicWords

open PowerSeries Finset Langlands.FormalPowerSeries

section Filtration

variable {R : Type*} [Ring R]

private def AgreeBelow (n : ℕ) (f g : PowerSeries R) : Prop := VanishesBelow n (f - g)

private theorem agreeBelow_iff {n : ℕ} {f g : PowerSeries R} :
    AgreeBelow n f g ↔ ∀ m < n, coeff m f = coeff m g := by
  simp only [AgreeBelow, VanishesBelow, map_sub, sub_eq_zero]

private theorem AgreeBelow.refl (n : ℕ) (f : PowerSeries R) : AgreeBelow n f f :=
  agreeBelow_iff.mpr fun _ _ => rfl

private theorem AgreeBelow.trans {n : ℕ} {f g h : PowerSeries R}
    (hfg : AgreeBelow n f g) (hgh : AgreeBelow n g h) : AgreeBelow n f h :=
  agreeBelow_iff.mpr fun m hm => (agreeBelow_iff.mp hfg m hm).trans (agreeBelow_iff.mp hgh m hm)

private theorem AgreeBelow.mono {m n : ℕ} {f g : PowerSeries R} (h : AgreeBelow n f g) (hmn : m ≤ n) :
    AgreeBelow m f g := fun k hk => h k (hk.trans_le hmn)

private theorem AgreeBelow.add {n : ℕ} {f₁ f₂ g₁ g₂ : PowerSeries R}
    (hf : AgreeBelow n f₁ f₂) (hg : AgreeBelow n g₁ g₂) : AgreeBelow n (f₁ + g₁) (f₂ + g₂) :=
  agreeBelow_iff.mpr fun m hm => by rw [map_add, map_add, agreeBelow_iff.mp hf m hm, agreeBelow_iff.mp hg m hm]

private theorem AgreeBelow.mul {n : ℕ} {f₁ f₂ g₁ g₂ : PowerSeries R}
    (hf : AgreeBelow n f₁ f₂) (hg : AgreeBelow n g₁ g₂) : AgreeBelow n (f₁ * g₁) (f₂ * g₂) := by
  apply agreeBelow_iff.mpr
  intro m hm
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hsum := Finset.mem_antidiagonal.mp hp
  rw [agreeBelow_iff.mp hf _ (by omega), agreeBelow_iff.mp hg _ (by omega)]

private theorem AgreeBelow.pow {n : ℕ} {f g : PowerSeries R}
    (h : AgreeBelow n f g) (k : ℕ) : AgreeBelow n (f ^ k) (g ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using refl n (1 : PowerSeries R)
  | succ k ih => simpa only [pow_succ] using ih.mul h

private theorem VanishesBelow.coeff_mul_left {f g : PowerSeries R} {n : ℕ} (hg : VanishesBelow n g) :
    coeff n (f * g) = coeff 0 f * coeff n g := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
  · intro p hp hne
    have hsum := Finset.mem_antidiagonal.mp hp
    have hlt : p.2 < n := by
      by_contra! h
      exact hne (Prod.ext (by omega) (by omega))
    rw [hg _ hlt, mul_zero]
  · intro hn
    exact (hn (Finset.mem_antidiagonal.mpr (zero_add _))).elim

private theorem vanishesBelow_one_of_constantCoeff {f : PowerSeries R} (hf : constantCoeff f = 0) :
    VanishesBelow 1 f := fun m hm => by
  have : m = 0 := by omega
  simpa only [this, coeff_zero_eq_constantCoeff_apply] using hf

private theorem coeff_inv_zero (u : (PowerSeries R)ˣ) (hu : constantCoeff (u : PowerSeries R) = 1) :
    coeff 0 (↑u⁻¹ : PowerSeries R) = 1 := by
  have h : constantCoeff ((u : PowerSeries R) * (↑u⁻¹ : PowerSeries R)) = 1 := by
    rw [Units.mul_inv, map_one]
  rw [map_mul, hu, one_mul] at h
  rwa [coeff_zero_eq_constantCoeff_apply]

end Filtration

section Exponential

variable (F : Type*) [Field F] {R : Type*} [Ring R] [Algebra F R]

private theorem AgreeBelow.smul {n : ℕ} {f g : PowerSeries R} (h : AgreeBelow n f g) (a : F) :
    AgreeBelow n (a • f) (a • g) := agreeBelow_iff.mpr fun m hm => by
  rw [coeff_smul, coeff_smul, agreeBelow_iff.mp h m hm]

private theorem coeff_formalExponential_sub {n : ℕ} {f g : PowerSeries R}
    (hf : VanishesBelow 1 f) (hg : VanishesBelow 1 g) (h : AgreeBelow n f g) {m : ℕ} (hm : m ≤ n) :
    coeff m (formalExponential F f - formalExponential F g) = coeff m (f - g) := by
  have hHigh (k : ℕ) : coeff m (f ^ (k + 2)) = coeff m (g ^ (k + 2)) := by
    have hA := (show VanishesBelow n (f ^ (k + 1) - g ^ (k + 1)) from h.pow (k + 1)).mul hf
    have hB := (hg.pow (k + 1)).mul (show VanishesBelow n (f - g) from h)
    have hDiff : f ^ (k + 2) - g ^ (k + 2) =
        (f ^ (k + 1) - g ^ (k + 1)) * f + g ^ (k + 1) * (f - g) := by
      rw [pow_succ f (k + 1), pow_succ g (k + 1)]
      noncomm_ring
    have he := congrArg (coeff m) hDiff
    rw [map_sub, map_add, hA m (by omega), hB m (by omega), add_zero, sub_eq_zero] at he
    exact he
  rw [map_sub, coeff_formalExponential_of_le F hf (Nat.le_succ m),
    coeff_formalExponential_of_le F hg (Nat.le_succ m), ← map_sub]
  unfold exponentialPartial
  rw [← Finset.sum_sub_distrib, map_sum, Finset.sum_range_succ', Finset.sum_range_succ']
  have hTerms (k : ℕ) : coeff m (((((k + 2).factorial : F)⁻¹) • f ^ (k + 2)) -
      ((((k + 2).factorial : F)⁻¹) • g ^ (k + 2))) = 0 := by
    rw [map_sub, coeff_smul, coeff_smul, hHigh, sub_self]
  simp [hTerms, Nat.add_assoc]

private theorem AgreeBelow.exp {n : ℕ} {f g : PowerSeries R}
    (h : AgreeBelow n f g) (hf : VanishesBelow 1 f) (hg : VanishesBelow 1 g) :
    AgreeBelow n (formalExponential F f) (formalExponential F g) := fun m hm => by
  rw [coeff_formalExponential_sub F hf hg h hm.le, h m hm]

end Exponential

section WordSeries

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [CharZero F]

local notation "Series" => PowerSeries (WordPolynomial F)
local notation "tr" => seriesTrace (cyclicTrace F)

/-- The letter as a series in degree one. -/
def seriesLetter (b : Bool) : Series := PowerSeries.monomial 1 (letter b)

private def conjugate (u : Seriesˣ) (f : Series) : Series := (u : Series) * f * (↑u⁻¹ : Series)

private def shiftedExponent (s : F) (u v : Seriesˣ) : Series :=
  s • (conjugate u (seriesLetter false) + conjugate v (seriesLetter true))

private def productExponential (s : F) : Seriesˣ :=
  exponentialUnit F (s • seriesLetter false) * exponentialUnit F (s • seriesLetter true)

omit [IsUltrametricDist F] [CharZero F] in
private theorem productExponential_const (s : F) : constantCoeff (productExponential s : Series) = 1 := by
  change constantCoeff (formalExponential F (s • seriesLetter false) *
    formalExponential F (s • seriesLetter true)) = 1
  simp

omit [IsUltrametricDist F] [CharZero F] in
theorem seriesLetter_control (b : Bool) : WordSeriesControl 1 (seriesLetter (F := F) b) :=
  WordSeriesControl.monomial (by
    simpa only [FreeMonoid.length_of, norm_one, letter] using
      WordPolynomialControl.single (FreeMonoid.of b) (1 : F))

omit [IsUltrametricDist F] [CharZero F] in
private theorem constantCoeff_seriesLetter (b : Bool) : constantCoeff (seriesLetter (F := F) b) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, seriesLetter, coeff_monomial]
  simp

omit [IsUltrametricDist F] [CharZero F] in
private theorem vanishesBelow_scaledLetter (s : F) (b : Bool) : VanishesBelow 1 (s • seriesLetter (F := F) b) :=
  vanishesBelow_one_of_constantCoeff (by rw [constantCoeff_smul, constantCoeff_seriesLetter, smul_zero])

omit [IsUltrametricDist F] [CharZero F] in
private theorem vanishesBelow_shiftedExponent (s : F) (u v : Seriesˣ) : VanishesBelow 1 (shiftedExponent s u v) := by
  apply vanishesBelow_one_of_constantCoeff
  simp [shiftedExponent, conjugate, constantCoeff_seriesLetter]

omit [CharZero F] in
theorem WordSeriesControl.inv_unit (u : Seriesˣ) (hu₀ : constantCoeff (u : Series) = 1)
    (hu : WordSeriesControl 1 (u : Series)) : WordSeriesControl 1 (↑u⁻¹ : Series) := by
  have h : unitOfConstantOne (u : Series) hu₀ = u := Units.ext rfl
  exact h ▸ hu.invOfUnit

omit [CharZero F] in
private theorem shiftedExponent_control (s : F) (u v : Seriesˣ)
    (hu₀ : constantCoeff (u : Series) = 1) (hv₀ : constantCoeff (v : Series) = 1)
    (hu : WordSeriesControl 1 (u : Series)) (hv : WordSeriesControl 1 (v : Series)) :
    WordSeriesControl ‖s‖ (shiftedExponent s u v) := by
  have hConj (k : Seriesˣ) (hk₀ : constantCoeff (k : Series) = 1)
      (hk : WordSeriesControl 1 (k : Series)) (b : Bool) : WordSeriesControl 1 (conjugate k (seriesLetter b)) := by
    simpa only [conjugate, mul_one] using (hk.mul (seriesLetter_control b)).mul (WordSeriesControl.inv_unit k hk₀ hk)
  simpa only [shiftedExponent, mul_one] using ((hConj u hu₀ hu false).add (hConj v hv₀ hv true)).smul s

omit [CharZero F] in
private theorem error_control (s : F) (hsmall : ‖s‖ ≤ 1)
    (hFac : ∀ k : ℕ, 0 < k → ‖((k.factorial : F)⁻¹)‖ * ‖s‖ ^ k ≤ ‖s‖)
    (u v : Seriesˣ) (hu₀ : constantCoeff (u : Series) = 1) (hv₀ : constantCoeff (v : Series) = 1)
    (hu : WordSeriesControl 1 (u : Series)) (hv : WordSeriesControl 1 (v : Series)) :
    WordSeriesControl ‖s‖ ((productExponential s : Series) - formalExponential F (shiftedExponent s u v)) := by
  have hL (b : Bool) : WordSeriesControl ‖s‖ (s • seriesLetter (F := F) b) := by
    simpa only [mul_one] using (seriesLetter_control b).smul s
  have hR := WordSeriesControl.exponentialControl _ _ (shiftedExponent_control s u v hu₀ hv₀ hu hv) hFac
  have hP := WordSeriesControl.mul_sub_one hsmall
    (WordSeriesControl.exponentialControl _ _ (hL false) hFac)
    (WordSeriesControl.exponentialControl _ _ (hL true) hFac)
  change WordSeriesControl ‖s‖ ((productExponential s : Series) - 1) at hP
  have he : (productExponential s : Series) - 1 - (formalExponential F (shiftedExponent s u v) - 1) =
      (productExponential s : Series) - formalExponential F (shiftedExponent s u v) := by abel
  simpa only [he] using hP.sub hR

omit [IsUltrametricDist F] in
private theorem error_trace (s : F) (u v : Seriesˣ) {n : ℕ} (hn : 0 < n)
    (h : AgreeBelow n (productExponential s : Series) (formalExponential F (shiftedExponent s u v))) :
    cyclicTrace F (coeff n ((productExponential s : Series) - formalExponential F (shiftedExponent s u v))) = 0 := by
  let τ := cyclicTrace F
  have hτ := cyclicTrace_mul_comm F
  have hP := vanishesBelow_shiftedExponent s u v
  have hExp := formalExponentialTrace F τ hτ _ hP
  have hPr := seriesTrace_logarithmicEuler_mul τ hτ (exponentialUnit F (s • seriesLetter false))
    (exponentialUnit F (s • seriesLetter true))
  rw [formalExponentialTrace F τ hτ _ (vanishesBelow_scaledLetter s false),
    formalExponentialTrace F τ hτ _ (vanishesBelow_scaledLetter s true)] at hPr
  have hTraceEuler : tr (euler (F := F) (shiftedExponent s u v)) =
      tr (euler (F := F) (s • seriesLetter false)) + tr (euler (F := F) (s • seriesLetter true)) := by
    funext m
    simp only [Pi.add_apply, seriesTrace_apply, coeff_euler, map_nsmul, shiftedExponent, coeff_smul,
      map_add, map_smul]
    have hx := congrFun (seriesTrace_conjugate τ hτ u (seriesLetter false)) m
    have hy := congrFun (seriesTrace_conjugate τ hτ v (seriesLetter true)) m
    change cyclicTrace F (coeff m (conjugate u (seriesLetter false))) = _ at hx
    change cyclicTrace F (coeff m (conjugate v (seriesLetter true))) = _ at hy
    rw [hx, hy, smul_add]
    simp only [Pi.smul_apply, seriesTrace_apply, coeff_euler, map_nsmul, τ]
  apply trace_coeff_sub_eq_zero_of_logarithmicEuler F τ (productExponential s)
    (exponentialUnit F (shiftedExponent s u v))
  · exact productExponential_const s
  · exact hn
  · exact h
  · exact hPr.trans ((hExp.trans hTraceEuler).symm)

private def correction (d : ℕ) (a : WordPolynomial F) : Series := 1 + PowerSeries.monomial d a

omit [IsUltrametricDist F] [CharZero F] in
private theorem correction_const {d : ℕ} (hd : 0 < d) (a : WordPolynomial F) :
    constantCoeff (correction d a) = 1 := by
  rw [correction, map_add, map_one, ← coeff_zero_eq_constantCoeff_apply, coeff_monomial,
    ite_eq_right hd.ne, add_zero]

private def corrected (u : Seriesˣ) {d : ℕ} (hd : 0 < d) (a : WordPolynomial F) : Seriesˣ :=
  u * unitOfConstantOne (correction d a) (correction_const hd a)

omit [IsUltrametricDist F] [CharZero F] in
private theorem corrected_const (u : Seriesˣ) (hu : constantCoeff (u : Series) = 1)
    {d : ℕ} (hd : 0 < d) (a : WordPolynomial F) : constantCoeff (corrected u hd a : Series) = 1 := by
  change constantCoeff ((u : Series) * correction d a) = 1
  rw [map_mul, hu, correction_const hd, mul_one]

omit [CharZero F] in
private theorem corrected_control (u : Seriesˣ) (hu : WordSeriesControl 1 (u : Series))
    {d : ℕ} (hd : 0 < d) {a : WordPolynomial F} (ha : WordPolynomialControl d 1 a) :
    WordSeriesControl 1 (corrected u hd a : Series) := by
  change WordSeriesControl 1 ((u : Series) * correction d a)
  simpa only [correction, mul_one] using hu.mul (WordSeriesControl.one.add (WordSeriesControl.monomial ha))

omit [IsUltrametricDist F] [CharZero F] in
private theorem corrected_agrees (u : Seriesˣ) {d : ℕ} (hd : 0 < d) (a : WordPolynomial F) :
    AgreeBelow d (corrected u hd a : Series) (u : Series) := by
  have hMon : VanishesBelow d (PowerSeries.monomial d a) := fun m hm => by
    rw [coeff_monomial, ite_eq_right hm.ne]
  have hEq : (corrected u hd a : Series) - (u : Series) = (u : Series) * PowerSeries.monomial d a := by
    change (u : Series) * (1 + PowerSeries.monomial d a) - (u : Series) = _
    rw [mul_add, mul_one, add_sub_cancel_left]
  change VanishesBelow d ((corrected u hd a : Series) - (u : Series))
  rw [hEq]
  exact hMon.mul_left _

omit [IsUltrametricDist F] [CharZero F] in
private theorem correction_conjugate_diff (u : Seriesˣ) (hu : constantCoeff (u : Series) = 1)
    {d : ℕ} (hd : 0 < d) (a : WordPolynomial F) (b : Bool) :
    let f := conjugate (corrected u hd a) (seriesLetter b) - conjugate u (seriesLetter b)
    VanishesBelow (d + 1) f ∧ coeff (d + 1) f = a * letter b - letter b * a := by
  let k := unitOfConstantOne (correction d a) (correction_const hd a)
  let f := seriesLetter (F := F) b
  let p := PowerSeries.monomial (d + 1) (a * letter b - letter b * a)
  have hp : VanishesBelow (d + 1) p := fun m hm => by
    rw [show p = _ from rfl, coeff_monomial, ite_eq_right hm.ne]
  have hp₁ : coeff (d + 1) p = a * letter b - letter b * a := coeff_monomial_same _ _
  have hComm : (k : Series) * f - f * (k : Series) = p := by
    change (1 + PowerSeries.monomial d a) * PowerSeries.monomial 1 (letter b) -
      PowerSeries.monomial 1 (letter b) * (1 + PowerSeries.monomial d a) = p
    rw [add_mul, mul_add, one_mul, mul_one, monomial_mul_monomial, monomial_mul_monomial, Nat.add_comm 1 d]
    simp only [p, map_sub]
    abel
  have hEq : conjugate (corrected u hd a) f - conjugate u f =
      (u : Series) * (p * (↑k⁻¹ : Series)) * (↑u⁻¹ : Series) := by
    rw [← hComm]
    simp only [conjugate, corrected, k, Units.val_mul, mul_inv_rev, sub_mul, mul_sub, mul_assoc,
      Units.mul_inv_cancel_left]
  change VanishesBelow (d + 1) (conjugate (corrected u hd a) f - conjugate u f) ∧ _
  rw [hEq]
  have hV := (hp.mul_right (↑k⁻¹ : Series)).mul_left (u : Series)
  refine ⟨hV.mul_right _, ?_⟩
  rw [hV.coeff_mul, VanishesBelow.coeff_mul_left (hp.mul_right (↑k⁻¹ : Series)), hp.coeff_mul, hp₁,
    coeff_inv_zero u hu, coeff_inv_zero k (correction_const hd a), coeff_zero_eq_constantCoeff_apply, hu,
    mul_one, one_mul, mul_one]

private structure Approximation (s : F) (n : ℕ) where
  left : Seriesˣ
  right : Seriesˣ
  left_const : constantCoeff (left : Series) = 1
  right_const : constantCoeff (right : Series) = 1
  left_control : WordSeriesControl 1 (left : Series)
  right_control : WordSeriesControl 1 (right : Series)
  agreement : AgreeBelow (n + 2) (productExponential s : Series)
    (formalExponential F (shiftedExponent s left right))

private def firstApproximation (s : F) : Approximation s 0 where
  left := 1
  right := 1
  left_const := map_one _
  right_const := map_one _
  left_control := WordSeriesControl.one
  right_control := WordSeriesControl.one
  agreement := by
    apply agreeBelow_iff.mpr
    intro m hm
    have hCoeff (f : Series) (hf : VanishesBelow 1 f) : coeff 1 (formalExponential F f) = coeff 1 f := by
      simp only [formalExponential, coeff_mk, exponentialPartial]
      simp [Finset.sum_range_succ, PowerSeries.coeff_one]
    have hConst := productExponential_const s
    have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl
    · simpa only [coeff_zero_eq_constantCoeff_apply, constantCoeff_formalExponential] using hConst
    · change coeff 1 (formalExponential F (s • seriesLetter false) * formalExponential F (s • seriesLetter true)) = _
      have hMul (p q : Series) : coeff 1 (p * q) = constantCoeff p * coeff 1 q + coeff 1 p * constantCoeff q := by
        rw [coeff_mul, show Finset.antidiagonal 1 = {(0, 1), (1, 0)} from rfl,
          Finset.sum_insert (by decide), Finset.sum_singleton]
        simp only [coeff_zero_eq_constantCoeff_apply]
      rw [hMul, constantCoeff_formalExponential, constantCoeff_formalExponential,
        one_mul, mul_one, add_comm, hCoeff _ (vanishesBelow_scaledLetter s _), hCoeff _ (vanishesBelow_scaledLetter s _),
        hCoeff _ (vanishesBelow_shiftedExponent s _ _)]
      simp only [shiftedExponent, conjugate, Units.val_one, inv_one, one_mul, mul_one, coeff_smul, map_add, smul_add]

private theorem extendApproximation (s : F) (hs : s ≠ 0) (hsmall : ‖s‖ ≤ 1)
    (hFac : ∀ k : ℕ, 0 < k → ‖((k.factorial : F)⁻¹)‖ * ‖s‖ ^ k ≤ ‖s‖)
    (n : ℕ) (old : Approximation s n) :
    ∃ new : Approximation s (n + 1),
      AgreeBelow (n + 1) (new.left : Series) (old.left : Series) ∧
      AgreeBelow (n + 1) (new.right : Series) (old.right : Series) := by
  let P := shiftedExponent s old.left old.right
  let W := (productExponential s : Series)
  let p := coeff (n + 2) (W - formalExponential F P)
  have hp : WordPolynomialControl (n + 2) ‖s‖ p :=
    error_control s hsmall hFac old.left old.right old.left_const old.right_const old.left_control old.right_control _
  have hTrace : cyclicTrace F p = 0 := error_trace s old.left old.right (by omega) old.agreement
  have hBound : WordPolynomialControl (n + 2) 1 (s⁻¹ • p) := by
    simpa only [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs)] using hp.smul s⁻¹
  obtain ⟨a, b, ha, hb, hNorm, hSplit⟩ := cyclicWordSplitting F (n + 1) 1 zero_le_one
    (s⁻¹ • p) hBound.graded hBound.norm_le (by rw [map_smul, hTrace, smul_zero])
  let u := corrected old.left (Nat.succ_pos n) a
  let v := corrected old.right (Nat.succ_pos n) b
  let Q := shiftedExponent s u v
  obtain ⟨hu, hu₁⟩ := correction_conjugate_diff old.left old.left_const (Nat.succ_pos n) a false
  obtain ⟨hv, hv₁⟩ := correction_conjugate_diff old.right old.right_const (Nat.succ_pos n) b true
  have hDiff : Q - P = s • ((conjugate u (seriesLetter false) - conjugate old.left (seriesLetter false)) +
      (conjugate v (seriesLetter true) - conjugate old.right (seriesLetter true))) := by
    dsimp only [Q, P, shiftedExponent]
    rw [← smul_sub]
    congr 1
    abel
  have hLow : AgreeBelow (n + 2) Q P := fun k hk => by
    rw [hDiff, coeff_smul, map_add, hu k hk, hv k hk, add_zero, smul_zero]
  have hTop : coeff (n + 2) (Q - P) = p := by
    rw [hDiff, coeff_smul, map_add, hu₁, hv₁, ← hSplit, smul_smul, mul_inv_cancel₀ hs, one_smul]
  let hQ := vanishesBelow_shiftedExponent s u v
  let hP := vanishesBelow_shiftedExponent s old.left old.right
  have hAg : AgreeBelow (n + 1 + 2) W (formalExponential F Q) := by
    intro m hm
    have hDiffE : coeff m (formalExponential F Q - formalExponential F P) = coeff m (Q - P) :=
      coeff_formalExponential_sub F hQ hP hLow (by omega)
    have he : coeff m (W - formalExponential F Q) =
        coeff m (W - formalExponential F P) - coeff m (formalExponential F Q - formalExponential F P) := by
      simp only [map_sub]
      abel
    rw [he, hDiffE]
    by_cases h : m < n + 2
    · rw [old.agreement m h, hLow m h, sub_zero]
    · have hm' : m = n + 2 := by omega
      rw [hm', hTop, sub_self]
  exact ⟨⟨u, v, corrected_const _ old.left_const _ _, corrected_const _ old.right_const _ _,
    corrected_control _ old.left_control _ ⟨ha, fun w => (hNorm w).1⟩,
    corrected_control _ old.right_control _ ⟨hb, fun w => (hNorm w).2⟩, hAg⟩,
    corrected_agrees _ (Nat.succ_pos n) a, corrected_agrees _ (Nat.succ_pos n) b⟩

/-- The formal straightening of the product of two scaled letter exponentials by
unit conjugators of coefficient bound one and constant coefficient one. -/
def FormalExponentialStraighteningStatement (F : Type*) [NontriviallyNormedField F]
    [IsUltrametricDist F] [CharZero F] (s : F) : Prop :=
  s ≠ 0 → ‖s‖ ≤ 1 → (∀ k : ℕ, 0 < k → ‖((k.factorial : F)⁻¹)‖ * ‖s‖ ^ k ≤ ‖s‖) →
  let S := PowerSeries (WordPolynomial F)
  ∃ u v : Sˣ,
    constantCoeff (u : S) = 1 ∧ constantCoeff (v : S) = 1 ∧
    WordSeriesControl 1 (u : S) ∧ WordSeriesControl 1 (v : S) ∧
    formalExponential F (s • ((u : S) * seriesLetter false * (↑u⁻¹ : S) +
      (v : S) * seriesLetter true * (↑v⁻¹ : S))) =
      formalExponential F (s • seriesLetter false) * formalExponential F (s • seriesLetter true)

set_option maxHeartbeats 3500000 in
theorem formalExponentialStraightening (s : F) : FormalExponentialStraighteningStatement F s := by
  intro hs hsmall hFac
  let step (n : ℕ) (p : Approximation s n) := Classical.choose (extendApproximation s hs hsmall hFac n p)
  let seq : ∀ n : ℕ, Approximation s n := Nat.rec (firstApproximation s) step
  have hStep (n : ℕ) :
      AgreeBelow (n + 1) ((seq (n + 1)).left : Series) ((seq n).left : Series) ∧
      AgreeBelow (n + 1) ((seq (n + 1)).right : Series) ((seq n).right : Series) :=
    Classical.choose_spec (extendApproximation s hs hsmall hFac n (seq n))
  have hStabilizes (m n : ℕ) (hmn : m ≤ n) :
      coeff m ((seq n).left : Series) = coeff m ((seq m).left : Series) ∧
      coeff m ((seq n).right : Series) = coeff m ((seq m).right : Series) := by
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ n hmn ih =>
      have hm : m < n + 1 := by omega
      exact ⟨(agreeBelow_iff.mp (hStep n).1 m hm).trans ih.1, (agreeBelow_iff.mp (hStep n).2 m hm).trans ih.2⟩
  let f : Series := PowerSeries.mk (fun n => coeff n ((seq n).left : Series))
  let g : Series := PowerSeries.mk (fun n => coeff n ((seq n).right : Series))
  have hf : constantCoeff f = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, show f = _ from rfl, coeff_mk, coeff_zero_eq_constantCoeff_apply]
    exact (seq 0).left_const
  have hg : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, show g = _ from rfl, coeff_mk, coeff_zero_eq_constantCoeff_apply]
    exact (seq 0).right_const
  let u := unitOfConstantOne f hf
  let v := unitOfConstantOne g hg
  have hUf : WordSeriesControl 1 f := fun n => by simpa only [f, coeff_mk] using (seq n).left_control n
  have hVg : WordSeriesControl 1 g := fun n => by simpa only [g, coeff_mk] using (seq n).right_control n
  refine ⟨u, v, hf, hg, hUf, hVg, ?_⟩
  change formalExponential F (shiftedExponent s u v) = (productExponential s : Series)
  apply PowerSeries.ext
  intro n
  have hu : AgreeBelow (n + 1) (u : Series) ((seq n).left : Series) := agreeBelow_iff.mpr fun m hm => by
    change coeff m f = _
    exact (coeff_mk m _).trans (hStabilizes m n (by omega)).1.symm
  have hv : AgreeBelow (n + 1) (v : Series) ((seq n).right : Series) := agreeBelow_iff.mpr fun m hm => by
    change coeff m g = _
    exact (coeff_mk m _).trans (hStabilizes m n (by omega)).2.symm
  have hConj {k k' : Seriesˣ} (h : AgreeBelow (n + 1) (k : Series) (k' : Series)) (b : Bool) :
      AgreeBelow (n + 1) (conjugate k (seriesLetter b)) (conjugate k' (seriesLetter b)) :=
    (h.mul (AgreeBelow.refl _ _)).mul (VanishesBelow.inv_sub_inv h)
  have hQ : AgreeBelow (n + 1) (shiftedExponent s u v) (shiftedExponent s (seq n).left (seq n).right) :=
    AgreeBelow.smul F ((hConj hu false).add (hConj hv true)) s
  exact agreeBelow_iff.mp ((AgreeBelow.exp F hQ (vanishesBelow_shiftedExponent s u v)
    (vanishesBelow_shiftedExponent s (seq n).left (seq n).right)).trans
      (agreeBelow_iff.mpr fun m hm => (agreeBelow_iff.mp (seq n).agreement m (by omega)).symm)) n (Nat.lt_succ_self n)

end WordSeries

end Langlands.CyclicWords
