import Langlands.AlgebraicGeometry.LangWeil.Stepanov.Branch
import Langlands.AlgebraicGeometry.LangWeil.Stepanov.Norm

/-!
# Point branches of a plane curve

Let `P ∈ F[X][Y]` and let `(x, y) ∈ F × L` be a point of the curve `P = 0` over a field
extension `L / F` with `P_Y(x, y) ≠ 0`.  Specialising the universal branch substitution
`sigma P` at `(x, y)` and rescaling `S ↦ T / P_Y(x, y)²` gives a ring homomorphism
`rho P x y : F[X][Y] → L⟦T⟧` with `X ↦ x + T`; the image `branch P x y` of `Y` is a power
series root of `P(x + T, Y)` with constant term `y`.  The coefficient of `T^l` of `rho P x y A`
is `P_Y(x, y)^(-2l)` times the value at `(x, y)` of the coefficient of `S^l` of `sigma P A`.
In characteristic `p`, `q`-th powers (`q = p^k`) are constant modulo `T^q`, which computes the
low coefficients of `rho P x y (∑ B_i E_i^q)`.
-/

noncomputable section

universe u v

open Polynomial

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

variable {F : Type u} [Field F] {L : Type v} [Field L] [Algebra F L]

local notation "R2" => Polynomial (Polynomial F)

/-- Evaluation of `F[X][Y]` at the point `(x, y) ∈ F × L`. -/
def ev (x : F) (y : L) : R2 →+* L :=
  Polynomial.eval₂RingHom ((algebraMap F L).comp (Polynomial.evalRingHom x)) y

@[simp] theorem ev_C (x : F) (y : L) (p : Polynomial F) :
    ev x y (C p) = algebraMap F L (p.eval x) := by
  simp [ev]

@[simp] theorem ev_X (x : F) (y : L) : ev x y X = y := by
  simp [ev]

theorem ev_eq (x : F) (y : L) (A : R2) :
    ev x y A = ((A.map (Polynomial.evalRingHom x)).map (algebraMap F L)).eval y := by
  rw [Polynomial.map_map, Polynomial.eval_map]
  rfl

theorem constantCoeff_subst (c : R2) {Z : PowerSeries R2} (hZ : PowerSeries.X ∣ Z) (A : R2) :
    PowerSeries.constantCoeff (subst c Z A) = A := by
  have h : (PowerSeries.constantCoeff (R := R2)).comp (subst c Z) = RingHom.id R2 := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext r
        simp
      · simp
    · simp [PowerSeries.X_dvd_iff.mp hZ]
  exact DFunLike.congr_fun h A

theorem constantCoeff_sigma (P A : R2) : PowerSeries.constantCoeff (sigma P A) = A :=
  constantCoeff_subst _ (chi_dvd _ _) A

/-- The point branch homomorphism `A ↦ A(x + T, branch)`, obtained from `sigma P` by
evaluating at `(x, y)` and rescaling `S ↦ T / P_Y(x, y)²`. -/
def rho (P : R2) (x : F) (y : L) : R2 →+* PowerSeries L :=
  (PowerSeries.rescale ((ev x y (derivative P))⁻¹ ^ 2)).comp
    ((PowerSeries.map (ev x y)).comp (sigma P))

/-- The power series branch through `(x, y)`. -/
def branch (P : R2) (x : F) (y : L) : PowerSeries L := rho P x y X

theorem coeff_rho (P : R2) (x : F) (y : L) (A : R2) (l : ℕ) :
    PowerSeries.coeff l (rho P x y A) =
      ((ev x y (derivative P))⁻¹ ^ 2) ^ l * ev x y (PowerSeries.coeff l (sigma P A)) := by
  simp [rho, PowerSeries.coeff_rescale, PowerSeries.coeff_map]

theorem coeff_zero_rho (P : R2) (x : F) (y : L) (A : R2) :
    PowerSeries.coeff 0 (rho P x y A) = ev x y A := by
  rw [coeff_rho, pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_sigma]

theorem coeff_zero_branch (P : R2) (x : F) (y : L) : PowerSeries.coeff 0 (branch P x y) = y := by
  rw [branch, coeff_zero_rho, ev_X]

theorem rho_self (P : R2) (x : F) (y : L) (h : ev x y P = 0) : rho P x y P = 0 := by
  ext l
  rw [coeff_rho, sigma_self, PowerSeries.coeff_C]
  split_ifs with hl
  · simp [h]
  · simp

theorem rho_comp_C (P : R2) (x : F) (y : L) (hc : ev x y (derivative P) ≠ 0) :
    (rho P x y).comp C = iota L x := by
  apply Polynomial.ringHom_ext
  · intro a
    ext l
    simp only [RingHom.coe_comp, Function.comp_apply, coeff_rho]
    rw [iota_C, PowerSeries.coeff_C, sigma, subst_C_C, PowerSeries.coeff_C]
    split_ifs with hl
    · subst hl; simp
    · simp
  · ext l
    simp only [RingHom.coe_comp, Function.comp_apply, coeff_rho]
    rw [iota_X, sigma, subst_C_X]
    simp only [map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    rcases Nat.lt_trichotomy l 1 with hl | rfl | hl
    · obtain rfl : l = 0 := by omega
      simp
    · simp only [one_ne_zero, ite_false, ite_true, map_zero, zero_add, pow_one, mul_one, map_pow]
      rw [← mul_pow, inv_mul_cancel₀ hc, one_pow]
    · simp [show l ≠ 0 by omega, show l ≠ 1 by omega]

theorem rho_eq (P : R2) (x : F) (y : L) (hc : ev x y (derivative P) ≠ 0) :
    rho P x y = Polynomial.eval₂RingHom (iota L x) (branch P x y) := by
  apply Polynomial.ringHom_ext'
  · rw [rho_comp_C P x y hc]
    ext a <;> simp
  · simp [branch]

theorem rho_apply (P : R2) (x : F) (y : L) (hc : ev x y (derivative P) ≠ 0) (A : R2) :
    rho P x y A = (A.map (iota L x)).eval (branch P x y) := by
  rw [rho_eq P x y hc, Polynomial.eval_map]
  rfl

theorem eval_branch (P : R2) (x : F) (y : L) (hc : ev x y (derivative P) ≠ 0)
    (h : ev x y P = 0) : (P.map (iota L x)).eval (branch P x y) = 0 := by
  rw [← rho_apply P x y hc, rho_self P x y h]

/-! ### Frobenius modulo `T^q` -/

theorem X_pow_dvd_pow_sub_C {p : ℕ} [Fact p.Prime] [CharP L p] (k : ℕ) (Ψ : PowerSeries L) :
    PowerSeries.X ^ (p ^ k) ∣ Ψ ^ (p ^ k) - PowerSeries.C (PowerSeries.coeff 0 Ψ) ^ (p ^ k) := by
  have : CharP (PowerSeries L) p :=
    charP_of_injective_algebraMap (algebraMap L (PowerSeries L)).injective p
  rw [← sub_pow_char_pow]
  apply pow_dvd_pow_of_dvd
  rw [PowerSeries.X_dvd_iff]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Low coefficients of `rho P x y (∑ B_i E_i^q)` for `q = p^k`: the `q`-th powers may be
replaced by the `q`-th powers of their values at `(x, y)`. -/
theorem coeff_rho_sum_mul_pow {p : ℕ} [Fact p.Prime] [CharP L p] (k : ℕ) (P : R2) (x : F)
    (y : L) {ι : Type*} (s : Finset ι) (B E : ι → R2) {l : ℕ} (hl : l < p ^ k) :
    PowerSeries.coeff l (rho P x y (∑ i ∈ s, B i * E i ^ (p ^ k))) =
      ((ev x y (derivative P))⁻¹ ^ 2) ^ l *
        ∑ i ∈ s, ev x y (PowerSeries.coeff l (sigma P (B i))) * ev x y (E i) ^ (p ^ k) := by
  have key : ∀ i, PowerSeries.coeff l (rho P x y (B i * E i ^ (p ^ k))) =
      PowerSeries.coeff l (rho P x y (B i)) * ev x y (E i) ^ (p ^ k) := by
    intro i
    obtain ⟨D, hD⟩ := X_pow_dvd_pow_sub_C (p := p) k (rho P x y (E i))
    have h1 : rho P x y (E i) ^ (p ^ k) =
        PowerSeries.C (ev x y (E i) ^ (p ^ k)) + PowerSeries.X ^ (p ^ k) * D := by
      rw [← hD, coeff_zero_rho, map_pow]
      ring
    have h2 : PowerSeries.coeff l (rho P x y (B i) * (PowerSeries.X ^ (p ^ k) * D)) = 0 := by
      rw [mul_left_comm, PowerSeries.coeff_X_pow_mul']
      simp [not_le.mpr hl]
    rw [map_mul, map_pow, h1, mul_add, map_add, PowerSeries.coeff_mul_C, h2, add_zero]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key, coeff_rho]
  ring

/-! ### Multiplicity of a resultant at a point with several branches -/

/-- If `T ⊆ L` is a finite set of points `y` with `P(x, y) = 0 ≠ P_Y(x, y)` such that the first
`M` coefficients of `rho P x y A` vanish, then `Res_Y(P, A)` vanishes to order `≥ M · #T`
at `x`. -/
theorem mul_card_le_rootMultiplicity_of_rho (P A : R2) (D M : ℕ) (x : F) (T : Finset L)
    (hP : P ≠ 0) (hA : A.natDegree ≤ D) (hres : resultant P A P.natDegree D ≠ 0)
    (hT : ∀ y ∈ T, ev x y P = 0 ∧ ev x y (derivative P) ≠ 0 ∧
      ∀ l < M, PowerSeries.coeff l (rho P x y A) = 0) :
    M * T.card ≤ (resultant P A P.natDegree D).rootMultiplicity x := by
  classical
  have hinj : Set.InjOn (branch P x) (T : Set L) := by
    intro y _ y' _ h
    rw [← coeff_zero_branch P x y, ← coeff_zero_branch P x y', h]
  have hcard : (T.image (branch P x)).card = T.card := Finset.card_image_of_injOn hinj
  rw [← hcard]
  apply mul_card_le_rootMultiplicity_resultant (L := L) x P A D M _ hP hA hres
  · intro Φ hΦ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hΦ
    exact eval_branch P x y (hT y hy).2.1 (hT y hy).1
  · intro Φ hΦ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hΦ
    rw [← rho_apply P x y (hT y hy).2.1, PowerSeries.X_pow_dvd_iff]
    exact (hT y hy).2.2

end Langlands.AlgebraicGeometry.LangWeil.Stepanov
