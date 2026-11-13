import Langlands.AlgebraicGeometry.LangWeil.Stepanov.Taylor

/-!
# The universal scaled branch of a plane curve

For `P : F[X][Y]` with `Y`-derivative `c`, we construct a power series
`chi P ∈ F[X][Y]⟦S⟧` with zero constant term such that the substitution
`X ↦ X + c² S`, `Y ↦ Y + c · chi P` maps `P` to itself.  The series is the fixed
point of an explicit contraction built from the Taylor coefficients of `P`.  When `P`
lies in the box `(m, n)`, the coefficient of `S^l` of `chi P` lies in the box
`(-m + l(2m-1), 2-n + l(2n-2))`, so that the substitution respects explicit degree
bounds.
-/

noncomputable section

universe u

open Polynomial

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

variable {F : Type u} [CommRing F]

local notation "R2" => Polynomial (Polynomial F)

/-! ### A filtration on power series over `F[X][Y]` -/

/-- The coefficient of `S^l` in `Φ` lies in the box `(a + l α, b + l β)`. -/
def InW (α β a b : ℤ) (Φ : PowerSeries R2) : Prop :=
  ∀ l : ℕ, InBox (a + l * α) (b + l * β) (PowerSeries.coeff l Φ)

section InW

variable {α β : ℤ}

theorem inW_zero (a b : ℤ) : InW α β a b (0 : PowerSeries R2) := by
  intro l; simpa using inBox_zero (F := F) _ _

theorem InW.add {a b : ℤ} {Φ Ψ : PowerSeries R2} (h : InW α β a b Φ) (h' : InW α β a b Ψ) :
    InW α β a b (Φ + Ψ) := by
  intro l; simpa using (h l).add (h' l)

theorem InW.neg {a b : ℤ} {Φ : PowerSeries R2} (h : InW α β a b Φ) : InW α β a b (-Φ) := by
  intro l; simpa using (h l).neg

theorem InW.sub {a b : ℤ} {Φ Ψ : PowerSeries R2} (h : InW α β a b Φ) (h' : InW α β a b Ψ) :
    InW α β a b (Φ - Ψ) := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem InW.mono {a b a' b' : ℤ} {Φ : PowerSeries R2} (h : InW α β a b Φ) (ha : a ≤ a')
    (hb : b ≤ b') : InW α β a' b' Φ := fun l => (h l).mono (by linarith) (by linarith)

theorem InW.mul {a b a' b' : ℤ} {Φ Ψ : PowerSeries R2} (h : InW α β a b Φ)
    (h' : InW α β a' b' Ψ) : InW α β (a + a') (b + b') (Φ * Ψ) := by
  intro l
  rw [PowerSeries.coeff_mul]
  apply inBox_sum
  rintro ⟨i, j⟩ hij
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  refine ((h i).mul (h' j)).mono (le_of_eq ?_) (le_of_eq ?_) <;>
  · subst hij; push_cast; ring

theorem inW_sum {ι : Type*} (s : Finset ι) {a b : ℤ} (Φ : ι → PowerSeries R2)
    (h : ∀ i ∈ s, InW α β a b (Φ i)) : InW α β a b (∑ i ∈ s, Φ i) := by
  intro l
  rw [map_sum]
  exact inBox_sum s _ (fun i hi => h i hi l)

theorem inW_C {a b : ℤ} {P : R2} (h : InBox a b P) : InW α β a b (PowerSeries.C P) := by
  intro l
  rw [PowerSeries.coeff_C]
  split_ifs with hl
  · subst hl; simpa using h
  · exact inBox_zero _ _

theorem inW_X : InW α β (-α) (-β) (PowerSeries.X : PowerSeries R2) := by
  intro l
  rw [PowerSeries.coeff_X]
  split_ifs with hl
  · subst hl; simpa using inBox_one (F := F)
  · exact inBox_zero _ _

theorem InW.pow {a b : ℤ} {Φ : PowerSeries R2} (h : InW α β a b Φ) (k : ℕ) :
    InW α β (k * a) (k * b) (Φ ^ k) := by
  induction k with
  | zero => simpa using (inW_C (α := α) (β := β) (inBox_one (F := F)))
  | succ k ih =>
    rw [pow_succ]
    have := ih.mul h
    refine this.mono (le_of_eq ?_) (le_of_eq ?_) <;> push_cast <;> ring

end InW

/-! ### Taylor coefficients and the substitution -/

/-- The coefficient of `U^e₀ V^e₁` in `P(X + U, Y + V)`. -/
def tc (P : R2) (e₀ e₁ : ℕ) : R2 := ((theta P).coeff e₁).coeff e₀

theorem tc_zero_zero (P : R2) : tc P 0 0 = P := theta_coeff_zero_zero P

theorem tc_zero_one (P : R2) : tc P 0 1 = derivative P := theta_coeff_one_zero P

theorem inBox_tc {a b : ℤ} {P : R2} (h : InBox a b P) (e₀ e₁ : ℕ) :
    InBox (a - e₀) (b - e₁) (tc P e₀ e₁) :=
  inBox2_theta h e₁ e₀

/-- The substitution `X ↦ X + c² S`, `Y ↦ Y + c Z`, as a ring homomorphism
`F[X][Y] → F[X][Y]⟦S⟧`. -/
def subst (c : R2) (Z : PowerSeries R2) : R2 →+* PowerSeries R2 :=
  Polynomial.eval₂RingHom (R := Polynomial F) (S := PowerSeries R2)
    (Polynomial.eval₂RingHom (R := F) (S := PowerSeries R2)
      ((PowerSeries.C (R := R2)).comp ((C : Polynomial F →+* R2).comp C))
      (PowerSeries.C (C X) + PowerSeries.C (c ^ 2) * PowerSeries.X))
    (PowerSeries.C X + PowerSeries.C c * Z)

@[simp] theorem subst_C_C (c : R2) (Z : PowerSeries R2) (r : F) :
    subst c Z (C (C r)) = PowerSeries.C (C (C r)) := by
  simp [subst]

@[simp] theorem subst_C_X (c : R2) (Z : PowerSeries R2) :
    subst c Z (C X) = PowerSeries.C (C X) + PowerSeries.C (c ^ 2) * PowerSeries.X := by
  simp [subst]

@[simp] theorem subst_X (c : R2) (Z : PowerSeries R2) :
    subst c Z X = PowerSeries.C X + PowerSeries.C c * Z := by
  simp [subst]

/-- Evaluation of `F[X][Y][U][V]` at `U = c² S`, `V = c Z`. -/
def evUV (c : R2) (Z : PowerSeries R2) : Polynomial (Polynomial R2) →+* PowerSeries R2 :=
  Polynomial.eval₂RingHom (R := Polynomial R2) (S := PowerSeries R2)
    (Polynomial.eval₂RingHom (R := R2) (S := PowerSeries R2) (PowerSeries.C (R := R2))
      (PowerSeries.C (c ^ 2) * PowerSeries.X))
    (PowerSeries.C c * Z)

theorem evUV_comp_theta (c : R2) (Z : PowerSeries R2) :
    (evUV c Z).comp theta = subst c Z := by
  apply ringHom_ext'
  · apply ringHom_ext'
    · ext r
      simp [evUV]
    · simp [evUV]
  · simp [evUV]

/-- One term of the fixed-point map. -/
def bterm (c t : R2) (e₀ e₁ : ℕ) (Z : PowerSeries R2) : PowerSeries R2 :=
  if 2 ≤ 2 * e₀ + e₁ then
    PowerSeries.C (t * c ^ (2 * e₀ + e₁ - 2)) * PowerSeries.X ^ e₀ * Z ^ e₁
  else 0

/-- The fixed-point map `G`; the branch is its fixed point. -/
def branchMap (P c : R2) (Z : PowerSeries R2) : PowerSeries R2 :=
  -∑ e₁ ∈ (theta P).support, ∑ e₀ ∈ ((theta P).coeff e₁).support,
    bterm c (tc P e₀ e₁) e₀ e₁ Z

theorem term_identity (c t : R2) (e₀ e₁ : ℕ) (Z : PowerSeries R2) :
    PowerSeries.C t * (PowerSeries.C (c ^ 2) * PowerSeries.X) ^ e₀ * (PowerSeries.C c * Z) ^ e₁ =
      PowerSeries.C (c ^ 2) * bterm c t e₀ e₁ Z +
        ((if e₀ = 0 ∧ e₁ = 0 then PowerSeries.C t else 0) +
          (if e₀ = 0 ∧ e₁ = 1 then PowerSeries.C (t * c) * Z else 0)) := by
  by_cases h : 2 ≤ 2 * e₀ + e₁
  · have h1 : ¬ (e₀ = 0 ∧ e₁ = 0) := by omega
    have h2 : ¬ (e₀ = 0 ∧ e₁ = 1) := by omega
    simp only [bterm, h, h1, h2, ↓reduceIte, add_zero]
    obtain ⟨k, hk⟩ : ∃ k, 2 * e₀ + e₁ = k + 2 := ⟨2 * e₀ + e₁ - 2, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    have key : t * (c ^ 2) ^ e₀ * c ^ e₁ = c ^ 2 * (t * c ^ k) := by
      rw [← pow_mul, mul_assoc, ← pow_add, hk, pow_add]; ring
    calc PowerSeries.C t * (PowerSeries.C (c ^ 2) * PowerSeries.X) ^ e₀ *
          (PowerSeries.C c * Z) ^ e₁
        = PowerSeries.C (t * (c ^ 2) ^ e₀ * c ^ e₁) * PowerSeries.X ^ e₀ * Z ^ e₁ := by
          simp only [map_mul, map_pow]; ring
      _ = _ := by rw [key]; simp only [map_mul]; ring
  · obtain ⟨rfl, rfl | rfl⟩ : e₀ = 0 ∧ (e₁ = 0 ∨ e₁ = 1) := by omega
    · simp [bterm]
    · simp [bterm, map_mul]; ring

theorem sum_sum_ite_eq {A : Type*} [AddCommMonoid A] (Θ : Polynomial (Polynomial R2))
    (g : R2 → A) (hg : g 0 = 0) (a b : ℕ) :
    (∑ e₁ ∈ Θ.support, ∑ e₀ ∈ (Θ.coeff e₁).support,
      if e₀ = a ∧ e₁ = b then g ((Θ.coeff e₁).coeff e₀) else 0) = g ((Θ.coeff b).coeff a) := by
  have h1 : ∀ e₁, (∑ e₀ ∈ (Θ.coeff e₁).support,
      if e₀ = a ∧ e₁ = b then g ((Θ.coeff e₁).coeff e₀) else 0) =
      if e₁ = b then g ((Θ.coeff e₁).coeff a) else 0 := by
    intro e₁
    by_cases he : e₁ = b
    · simp only [he, and_true, ↓reduceIte]
      rw [Finset.sum_ite_eq']
      split_ifs with ha
      · rfl
      · rw [notMem_support_iff.mp ha, hg]
    · simp [he]
  rw [Finset.sum_congr rfl (fun e₁ _ => h1 e₁), Finset.sum_ite_eq']
  split_ifs with hb
  · rfl
  · rw [notMem_support_iff.mp hb, coeff_zero, hg]

/-- The basic identity: `P(X + c² S, Y + c Z) = P + P_Y c Z - c² G(Z)`. -/
theorem subst_eq (P c : R2) (Z : PowerSeries R2) :
    subst c Z P = PowerSeries.C P + PowerSeries.C (derivative P * c) * Z -
      PowerSeries.C (c ^ 2) * branchMap P c Z := by
  rw [← evUV_comp_theta, RingHom.comp_apply]
  simp only [evUV, coe_eval₂RingHom, eval₂_eq_sum, sum_def]
  simp only [Finset.sum_mul]
  have hterm : ∀ e₁ e₀, PowerSeries.C (((theta P).coeff e₁).coeff e₀) *
      (PowerSeries.C (c ^ 2) * PowerSeries.X) ^ e₀ * (PowerSeries.C c * Z) ^ e₁ =
      PowerSeries.C (c ^ 2) * bterm c (tc P e₀ e₁) e₀ e₁ Z +
        ((if e₀ = 0 ∧ e₁ = 0 then PowerSeries.C (((theta P).coeff e₁).coeff e₀) else 0) +
          (if e₀ = 0 ∧ e₁ = 1 then
            PowerSeries.C (((theta P).coeff e₁).coeff e₀ * c) * Z else 0)) := by
    intro e₁ e₀
    rw [term_identity]
    rfl
  simp only [hterm, Finset.sum_add_distrib]
  rw [sum_sum_ite_eq (theta P) (fun t => PowerSeries.C t) (by simp) 0 0,
    sum_sum_ite_eq (theta P) (fun t => PowerSeries.C (t * c) * Z) (by simp) 0 1]
  simp only [← Finset.mul_sum]
  rw [show ((theta P).coeff 0).coeff 0 = tc P 0 0 from rfl,
    show ((theta P).coeff 1).coeff 0 = tc P 0 1 from rfl, tc_zero_zero, tc_zero_one]
  unfold branchMap
  ring

/-! ### Contraction -/

theorem bterm_sub_dvd (c t : R2) (e₀ e₁ k : ℕ) {Z₁ Z₂ : PowerSeries R2}
    (h₁ : PowerSeries.X ∣ Z₁) (h₂ : PowerSeries.X ∣ Z₂)
    (h₁₂ : PowerSeries.X ^ k ∣ Z₁ - Z₂) :
    PowerSeries.X ^ (k + 1) ∣ bterm c t e₀ e₁ Z₁ - bterm c t e₀ e₁ Z₂ := by
  unfold bterm
  split_ifs with h
  swap
  · simp
  rw [show PowerSeries.C (t * c ^ (2 * e₀ + e₁ - 2)) * PowerSeries.X ^ e₀ * Z₁ ^ e₁ -
      PowerSeries.C (t * c ^ (2 * e₀ + e₁ - 2)) * PowerSeries.X ^ e₀ * Z₂ ^ e₁ =
      PowerSeries.C (t * c ^ (2 * e₀ + e₁ - 2)) * (PowerSeries.X ^ e₀ * (Z₁ ^ e₁ - Z₂ ^ e₁))
      by ring]
  apply Dvd.dvd.mul_left
  have hk : PowerSeries.X ^ k ∣ Z₁ ^ e₁ - Z₂ ^ e₁ := h₁₂.trans (sub_dvd_pow_sub_pow _ _ _)
  by_cases he₀ : 1 ≤ e₀
  · rw [pow_succ']
    exact mul_dvd_mul (dvd_pow_self _ (by omega)) hk
  · have he₁ : 2 ≤ e₁ := by omega
    have he₀' : e₀ = 0 := by omega
    subst he₀'
    rw [pow_zero, one_mul, ← geom_sum₂_mul, pow_succ, mul_comm (PowerSeries.X ^ k)]
    refine mul_dvd_mul ?_ h₁₂
    apply Finset.dvd_sum
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hi0 : i = 0
    · subst hi0
      exact Dvd.dvd.mul_left (dvd_pow h₂ (by omega)) _
    · exact Dvd.dvd.mul_right (dvd_pow h₁ hi0) _

theorem bterm_dvd (c t : R2) (e₀ e₁ : ℕ) {Z : PowerSeries R2} (h : PowerSeries.X ∣ Z) :
    PowerSeries.X ∣ bterm c t e₀ e₁ Z := by
  unfold bterm
  split_ifs with h2
  · by_cases he₀ : 1 ≤ e₀
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _) _
    · exact Dvd.dvd.mul_left (dvd_pow h (by omega)) _
  · exact dvd_zero _

theorem branchMap_sub_dvd (P c : R2) (k : ℕ) {Z₁ Z₂ : PowerSeries R2}
    (h₁ : PowerSeries.X ∣ Z₁) (h₂ : PowerSeries.X ∣ Z₂)
    (h₁₂ : PowerSeries.X ^ k ∣ Z₁ - Z₂) :
    PowerSeries.X ^ (k + 1) ∣ branchMap P c Z₁ - branchMap P c Z₂ := by
  unfold branchMap
  rw [neg_sub_neg, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro e₁ _
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro e₀ _
  exact bterm_sub_dvd c _ e₀ e₁ k h₂ h₁ (by rw [← neg_sub]; exact (dvd_neg).mpr h₁₂)

theorem branchMap_dvd (P c : R2) {Z : PowerSeries R2} (h : PowerSeries.X ∣ Z) :
    PowerSeries.X ∣ branchMap P c Z := by
  unfold branchMap
  apply (dvd_neg).mpr
  exact Finset.dvd_sum fun e₁ _ => Finset.dvd_sum fun e₀ _ => bterm_dvd c _ e₀ e₁ h

/-! ### The fixed point -/

/-- The iterates `G^k(0)`. -/
def chiSeq (P c : R2) : ℕ → PowerSeries R2
  | 0 => 0
  | k + 1 => branchMap P c (chiSeq P c k)

theorem chiSeq_dvd (P c : R2) (k : ℕ) : PowerSeries.X ∣ chiSeq P c k := by
  induction k with
  | zero => exact dvd_zero _
  | succ k ih => exact branchMap_dvd P c ih

theorem chiSeq_succ_sub_dvd (P c : R2) (k : ℕ) :
    PowerSeries.X ^ (k + 1) ∣ chiSeq P c (k + 1) - chiSeq P c k := by
  induction k with
  | zero => simpa [chiSeq] using branchMap_dvd P c (dvd_zero (PowerSeries.X : PowerSeries R2))
  | succ k ih =>
    exact branchMap_sub_dvd P c (k + 1) (chiSeq_dvd P c _) (chiSeq_dvd P c _) ih

theorem chiSeq_sub_dvd (P c : R2) {k j : ℕ} (hkj : k ≤ j) :
    PowerSeries.X ^ k ∣ chiSeq P c j - chiSeq P c k := by
  induction j, hkj using Nat.le_induction with
  | base => simp
  | succ j hkj ih =>
    rw [show chiSeq P c (j + 1) - chiSeq P c k =
      (chiSeq P c (j + 1) - chiSeq P c j) + (chiSeq P c j - chiSeq P c k) by ring]
    exact dvd_add ((pow_dvd_pow _ (by omega)).trans (chiSeq_succ_sub_dvd P c j)) ih

/-- The branch series: the limit of the iterates `G^k(0)`. -/
def chi (P c : R2) : PowerSeries R2 :=
  PowerSeries.mk fun l => PowerSeries.coeff l (chiSeq P c (l + 1))

theorem chi_sub_dvd (P c : R2) (k : ℕ) : PowerSeries.X ^ k ∣ chi P c - chiSeq P c k := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro l hl
  rw [map_sub, chi, PowerSeries.coeff_mk, sub_eq_zero]
  have h := chiSeq_sub_dvd P c (show l + 1 ≤ k by omega)
  rw [PowerSeries.X_pow_dvd_iff] at h
  have := h l (by omega)
  rw [map_sub, sub_eq_zero] at this
  exact this.symm

theorem chi_dvd (P c : R2) : PowerSeries.X ∣ chi P c := by
  have h := chi_sub_dvd P c 1
  rw [pow_one] at h
  have := dvd_add h (chiSeq_dvd P c 1)
  rwa [sub_add_cancel] at this

theorem branchMap_chi (P c : R2) : branchMap P c (chi P c) = chi P c := by
  rw [← sub_eq_zero]
  refine PowerSeries.ext fun l => ?_
  rw [map_zero]
  have h1 := branchMap_sub_dvd P c l (chi_dvd P c) (chiSeq_dvd P c l) (chi_sub_dvd P c l)
  have h2 := chi_sub_dvd P c (l + 1)
  have h : PowerSeries.X ^ (l + 1) ∣ branchMap P c (chi P c) - chi P c := by
    have := dvd_sub h1 h2
    rwa [show branchMap P c (chi P c) - branchMap P c (chiSeq P c l) -
      (chi P c - chiSeq P c (l + 1)) = branchMap P c (chi P c) - chi P c by
        simp only [chiSeq]; ring] at this
  rw [PowerSeries.X_pow_dvd_iff] at h
  exact h l (by omega)

/-- The fundamental identity of the branch: `P(X + c² S, Y + c χ) = P` for `c = P_Y`. -/
theorem subst_chi_self (P : R2) :
    subst (derivative P) (chi P (derivative P)) P = PowerSeries.C P := by
  rw [subst_eq]
  conv_lhs => rw [branchMap_chi]
  rw [show PowerSeries.C (derivative P * derivative P) =
    PowerSeries.C (derivative P ^ 2) by rw [sq]]
  ring


/-! ### Degree bounds for the branch -/

theorem inBox_derivative {a b : ℤ} {P : R2} (h : InBox a b P) :
    InBox a (b - 1) (derivative P) := by
  have := inBox_tc h 0 1
  rw [tc_zero_one] at this
  simpa using this

theorem inW_bterm {m n : ℤ} {P c : R2} (hP : InBox m n P) (hc : InBox m (n - 1) c)
    (e₀ e₁ : ℕ) {Z : PowerSeries R2} (hZ : InW (2 * m - 1) (2 * n - 2) (-m) (2 - n) Z) :
    InW (2 * m - 1) (2 * n - 2) (-m) (2 - n) (bterm c (tc P e₀ e₁) e₀ e₁ Z) := by
  unfold bterm
  split_ifs with h
  · obtain ⟨k, hk⟩ : ∃ k, 2 * e₀ + e₁ = k + 2 := ⟨2 * e₀ + e₁ - 2, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    have hk' : (k : ℤ) = 2 * e₀ + e₁ - 2 := by omega
    have h1 := ((inW_C (α := 2 * m - 1) (β := 2 * n - 2)
      ((inBox_tc hP e₀ e₁).mul (hc.pow k))).mul ((inW_X (F := F)).pow e₀)).mul (hZ.pow e₁)
    refine h1.mono (le_of_eq ?_) (le_of_eq ?_)
    · rw [hk']; ring
    · rw [hk']; ring
  · exact inW_zero _ _

theorem inW_branchMap {m n : ℤ} {P c : R2} (hP : InBox m n P) (hc : InBox m (n - 1) c)
    {Z : PowerSeries R2} (hZ : InW (2 * m - 1) (2 * n - 2) (-m) (2 - n) Z) :
    InW (2 * m - 1) (2 * n - 2) (-m) (2 - n) (branchMap P c Z) := by
  unfold branchMap
  exact (inW_sum _ _ fun e₁ _ => inW_sum _ _ fun e₀ _ => inW_bterm hP hc e₀ e₁ hZ).neg

theorem inW_chiSeq {m n : ℤ} {P c : R2} (hP : InBox m n P) (hc : InBox m (n - 1) c) (k : ℕ) :
    InW (2 * m - 1) (2 * n - 2) (-m) (2 - n) (chiSeq P c k) := by
  induction k with
  | zero => exact inW_zero _ _
  | succ k ih => exact inW_branchMap hP hc ih

/-- The branch has the weights `(-m, 2 - n)` for the filtration of slope `(2m - 1, 2n - 2)`. -/
theorem inW_chi {m n : ℤ} {P c : R2} (hP : InBox m n P) (hc : InBox m (n - 1) c) :
    InW (2 * m - 1) (2 * n - 2) (-m) (2 - n) (chi P c) := by
  intro l
  rw [chi, PowerSeries.coeff_mk]
  exact inW_chiSeq hP hc (l + 1) l

/-- The branch substitution `B ↦ B(X + P_Y² S, Y + P_Y χ)` attached to `P`. -/
def sigma (P : R2) : R2 →+* PowerSeries R2 := subst (derivative P) (chi P (derivative P))

theorem sigma_self (P : R2) : sigma P P = PowerSeries.C P := subst_chi_self P

/-- If `P` lies in the box `(m, n)` and `B` in the box `(a, b)`, then the coefficient of `S^l`
in `B(X + P_Y² S, Y + P_Y χ)` lies in the box `(a + l (2m - 1), b + l (2n - 2))`. -/
theorem inW_sigma {m n a b : ℤ} {P B : R2} (hP : InBox m n P) (hB : InBox a b B) :
    InW (2 * m - 1) (2 * n - 2) a b (sigma P B) := by
  have hc := inBox_derivative hP
  refine map_fil_of_inBox (sigma P) (InW (2 * m - 1) (2 * n - 2)) (fun a b => inW_zero a b)
    (fun a b x y hx hy => hx.add hy) (fun a b a' b' x y hx hy => hx.mul hy)
    (fun a b a' b' x ha hb hx => hx.mono ha hb) (fun r => ?_) ?_ ?_ hB
  · rw [sigma, subst_C_C]; exact inW_C (inBox_C_C r)
  · rw [sigma, subst_C_X]
    refine (inW_C inBox_C_X).add ?_
    have h2 := (inW_C (α := 2 * m - 1) (β := 2 * n - 2) (hc.pow 2)).mul (inW_X (F := F))
    refine h2.mono (le_of_eq ?_) (le_of_eq ?_) <;> push_cast <;> ring
  · rw [sigma, subst_X]
    refine (inW_C inBox_X).add ?_
    have h2 := (inW_C (α := 2 * m - 1) (β := 2 * n - 2) hc).mul (inW_chi hP hc)
    refine h2.mono (le_of_eq ?_) (le_of_eq ?_) <;> ring

end Langlands.AlgebraicGeometry.LangWeil.Stepanov
