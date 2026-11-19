import Langlands.Representation.Archimedean.RealAmbientAdjacentLifting
import Langlands.Representation.Archimedean.RealInducedPairPositiveGenericMiddle
import Langlands.Representation.Archimedean.RealLeviModes
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient

/-! # The diagonal character of the one-sided compact lift -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealCompactParityLifting

open Complex RealAmbientAdjacentLifting RealKTypeCount RealBlockJacquet
open RealBlockFourierFinite RealBlockFrobeniusDisjoint RealBlockRotation
open RealPolynomialFourierPropagation RealTailMultiplierPolynomial
open RealInducedPairPositiveGenericMiddle (modeSign)
open Polynomial (aeval eval)
open scoped Polynomial

local notation "Φ" => blockFourierCoefficient
private abbrev G (n : ℕ) := Langlands.GeneralLinear n ℝ

variable {n a D : ℕ}

private def raw (v : K n → ℂ) (g : G n) : ℂ := by
  classical
  exact if hg : g ∈ unitaryCompact ℝ n then v ⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩ else 0

private theorem raw_toUnits (v : K n → ℂ) (k : K n) :
    raw v (Unitary.toUnits k) = v k := by
  rw [raw, dite_eq_left (show Unitary.toUnits k ∈ unitaryCompact ℝ n from k.property)]
  rfl

private theorem restrict_raw (v : K n → ℂ) : restrictLinear n (raw v) = v :=
  funext (raw_toUnits v)

/-- A left Fourier coefficient of a compact function. Only its compact values
are used by the integral. -/
def compactCoeff (p : ℕ) (j : ℤ) (v : K n → ℂ) (x : K n) : ℂ :=
  Φ n p j (raw v) (Unitary.toUnits x)

theorem compactCoeff_restrict (p : ℕ) (j : ℤ) (f : G n → ℂ) (x : K n) :
    compactCoeff p j (restrictLinear n f) x = Φ n p j f (Unitary.toUnits x) := by
  apply blockFourierCoefficient_congr_on_compact _ x.property j
  intro g hg
  simp only [raw, dite_eq_left hg, restrictLinear_apply, toUnits_mk hg]

theorem projection_apply (ha : a + 3 ≤ n) {r : ℕ} (hr : r + 1 < 3)
    (j : ℤ) (v : degreeLE n D) (x : K n) :
    (projection ha hr j v : K n → ℂ) x =
      (2 * (Real.pi : ℂ))⁻¹ * compactCoeff (a + r) j v x := by
  let f := raw (v : K n → ℂ)
  have hf : restrictLinear n f ∈ degreeLE n D := (restrict_raw (v : K n → ℂ)).symm ▸ v.property
  have hv : (⟨restrictLinear n f, hf⟩ : degreeLE n D) = v := Subtype.ext (restrict_raw _)
  have h := projection_apply_restrict ha hr j f hf x
  rw [hv] at h
  exact h

/-- Left translation on a compact polynomial degree layer. -/
def left (g : K n) : Module.End ℂ (degreeLE n D) :=
  (leftAlgHom g).toLinearMap.restrict (p := degreeLE n D) (q := degreeLE n D)
    fun _ hv => left_mem_degreeLE hv g

@[simp] theorem left_apply (g : K n) (v : degreeLE n D) (x : K n) :
    (left g v : K n → ℂ) x = (v : K n → ℂ) (g * x) := rfl

private theorem left_comp (g h : K n) (v : degreeLE n D) :
    left g (left h v) = left (h * g) v := by
  apply Subtype.ext
  funext x
  simp only [left_apply, mul_assoc]

private theorem left_one (v : degreeLE n D) : left (1 : K n) v = v := by
  apply Subtype.ext
  funext x
  simp only [left_apply, one_mul]

private theorem left_injective (g : K n) : Function.Injective (left (D := D) g) := by
  intro u v h
  have hh := congrArg (left (D := D) g⁻¹) h
  simpa only [left_comp, mul_inv_cancel, left_one] using hh

abbrev inside (p : ℕ) (i : Fin n) := (i : ℕ) = p ∨ (i : ℕ) = p + 1

private def mode (p : ℕ) (i : Fin n) (j : ℤ) : ℤ := if inside p i then -j else j

private theorem compactCoeff_left_sign (p : ℕ) (hp : p + 1 < n) (i : Fin n)
    (j : ℤ) (v : K n → ℂ) (x : K n) :
    compactCoeff p j (fun k => v (signReflection n i * k)) x =
      compactCoeff p (mode p i j) v (signReflection n i * x) := by
  let s := Unitary.toUnits (signReflection n i)
  let f := raw v
  let f' : G n → ℂ := fun g => f (s * g)
  have hc : ∀ g, f' (s * g) = (1 : ℂ) * f g := by
    intro g
    change f (s * (s * g)) = 1 * f g
    rw [toUnits_signReflection_mul_mul_self, one_mul]
  have h := RealLeviModes.blockFourierCoefficient_signReflection_mul hp i hc j (s * Unitary.toUnits x)
  rw [toUnits_signReflection_mul_mul_self, one_mul] at h
  change Φ n p j f' (Unitary.toUnits x) =
    Φ n p (mode p i j) f (s * Unitary.toUnits x) at h
  change compactCoeff p j (fun k => v (signReflection n i * k)) x =
      Φ n p (mode p i j) f (s * Unitary.toUnits x)
  rw [← h]
  apply blockFourierCoefficient_congr_on_compact _ x.property j
  intro g hg
  let y : K n := ⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩
  rw [← toUnits_mk hg]
  change raw (fun k => v (signReflection n i * k)) (Unitary.toUnits y) =
    raw v (Unitary.toUnits (signReflection n i) * Unitary.toUnits y)
  rw [← map_mul, raw_toUnits, raw_toUnits]

private theorem projection_left_sign (ha : a + 3 ≤ n) {r : ℕ} (hr : r + 1 < 3)
    (i : Fin n) (j : ℤ) (v : degreeLE n D) :
    projection ha hr j (left (signReflection n i) v) =
      left (signReflection n i) (projection ha hr (mode (a + r) i j) v) := by
  apply Subtype.ext
  funext x
  rw [left_apply, projection_apply, projection_apply]
  exact congrArg ((2 * (Real.pi : ℂ))⁻¹ * ·)
    (compactCoeff_left_sign (a + r) (by omega) i j v x)

def compactRotation (p : ℕ) (θ : ℝ) : K n :=
  ⟨(blockRotation n p θ : Matrix (Fin n) (Fin n) ℝ), blockRotation_mem_unitaryCompact n p θ⟩

private theorem toUnits_compactRotation (p : ℕ) (θ : ℝ) :
    Unitary.toUnits (compactRotation (n := n) p θ) = blockRotation n p θ :=
  toUnits_mk (blockRotation_mem_unitaryCompact n p θ)

theorem compactRotation_pi {p : ℕ} (hp : p + 1 < n) :
    compactRotation p Real.pi = signReflection n (ia hp) * signReflection n (ib hp) := by
  apply Unitary.toUnits_injective
  rw [toUnits_compactRotation, map_mul, blockRotation_pi hp]

private theorem left_pi_projection (ha : a + 3 ≤ n) {r : ℕ} (hr : r + 1 < 3)
    (j : ℤ) (v : degreeLE n D) :
    left (compactRotation (a + r) Real.pi) (projection ha hr j v) =
      ((-1 : ℂ) ^ j) • projection ha hr j v := by
  apply Subtype.ext
  funext x
  change (left (compactRotation (a + r) Real.pi) (projection ha hr j v) : K n → ℂ) x =
    (-1 : ℂ) ^ j * (projection ha hr j v : K n → ℂ) x
  rw [left_apply, projection_apply, projection_apply]
  unfold compactCoeff
  rw [map_mul, toUnits_compactRotation,
    blockFourierCoefficient_blockRotation_mul (by omega : a + r + 1 < n)]
  have hz : Complex.exp ((j : ℂ) * (Real.pi : ℂ) * I) = (-1 : ℂ) ^ j := by
    rw [mul_assoc, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [hz, mul_left_comm]

private theorem tail_root_data {H : ℕ} {j : ℤ} (hj : (tailPolynomial H).eval (j : ℂ) = 0) :
    |j| < (H : ℤ) ∧ (-1 : ℂ) ^ j = (-1 : ℂ) ^ ((H : ℤ) - 1) := by
  rw [tailPolynomial_eval, descPochhammer_eval_eq_prod_range] at hj
  have hp : ∏ i ∈ Finset.range H, (((j : ℂ) + (H : ℂ) - 1) / 2 - (i : ℂ)) = 0 :=
    (div_eq_zero_iff.mp hj).resolve_right (by exact_mod_cast H.factorial_ne_zero)
  obtain ⟨i, hi, hz⟩ := Finset.prod_eq_zero_iff.mp hp
  have hz' : (j : ℂ) + (H : ℂ) - 1 = 2 * i := by linear_combination 2 * hz
  have hm : j + (H : ℤ) - 1 = 2 * (i : ℤ) := by exact_mod_cast hz'
  refine ⟨by
    rw [abs_lt]
    have := Finset.mem_range.mp hi
    omega, ?_⟩
  let f := (i : ℤ) - (H : ℤ) + 1
  have he : j = (H : ℤ) - 1 + 2 * f := by dsimp only [f]; omega
  rw [he, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
  norm_num

private theorem kernel_proj_zero (ha : a + 3 ≤ n) {s : ℕ} (hs : s + 1 < 3) {H : ℕ}
    {v : degreeLE n D} (hv : aeval (-I • generator ha hs) (tailPolynomial H) v = 0)
    {j : ℤ} (hj : (tailPolynomial H).eval (j : ℂ) ≠ 0) : projection ha hs j v = 0 := by
  have h := proj_aeval (ambient_modes ha hs) (tailPolynomial H) j v
  rw [hv, map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hj

theorem kernel_low (ha : a + 3 ≤ n) {s : ℕ} (hs : s + 1 < 3) {H : ℕ}
    {v : degreeLE n D} (hv : aeval (-I • generator ha hs) (tailPolynomial H) v = 0)
    {j : ℤ} (hj : (H : ℤ) ≤ |j|) : projection ha hs j v = 0 :=
  kernel_proj_zero ha hs hv (fun h => (not_lt_of_ge hj) (tail_root_data h).1)

private theorem kernel_eigen_pi (ha : a + 3 ≤ n) {s : ℕ} (hs : s + 1 < 3) {H : ℕ}
    {v : degreeLE n D} (hv : aeval (-I • generator ha hs) (tailPolynomial H) v = 0) :
    left (compactRotation (a + s) Real.pi) v = (-1 : ℂ) ^ ((H : ℤ) - 1) • v := by
  let hM := ambient_modes (D := D) ha hs
  conv_lhs => rw [← hM.sum_apply v]
  conv_rhs => rw [← hM.sum_apply v]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [left_pi_projection]
  by_cases hj : (tailPolynomial H).eval (j : ℂ) = 0
  · rw [(tail_root_data hj).2]
  · rw [kernel_proj_zero ha hs hv hj, smul_zero, smul_zero]

private theorem kernel_left_sign (ha : a + 3 ≤ n) {s : ℕ} (hs : s + 1 < 3) {H : ℕ}
    {v : degreeLE n D} (hv : aeval (-I • generator ha hs) (tailPolynomial H) v = 0)
    (i : Fin n) :
    aeval (-I • generator ha hs) (tailPolynomial H) (left (signReflection n i) v) = 0 := by
  let hM := ambient_modes (D := D) ha hs
  rw [← hM.sum_apply (aeval (-I • generator ha hs) (tailPolynomial H) (left (signReflection n i) v))]
  apply Finset.sum_eq_zero
  intro j _
  rw [proj_aeval hM, projection_left_sign]
  by_cases hj : (tailPolynomial H).eval (j : ℂ) = 0
  · rw [hj, zero_smul]
  have hmode : (tailPolynomial H).eval ((mode (a + s) i j : ℤ) : ℂ) ≠ 0 := by
    unfold mode
    split_ifs
    · rw [Int.cast_neg, tailPolynomial_neg]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hj
    · exact hj
  rw [kernel_proj_zero ha hs hv hmode, map_zero, smul_zero]

private theorem projection_halfturn {a r : ℕ} (ha : a + 3 ≤ 4) (hr : r + 1 < 3)
    (hp : a + r = 0 ∨ a + r = 2) (j : ℤ) (v : degreeLE 4 D) :
    projection ha hr j (left (compactRotation 1 Real.pi) v) =
      left (compactRotation 1 Real.pi) (projection ha hr (-j) v) := by
  have hR : compactRotation (n := 4) 1 Real.pi = signReflection 4 1 * signReflection 4 2 :=
    compactRotation_pi (p := 1) (by decide)
  rw [hR, ← left_comp]
  rw [projection_left_sign, projection_left_sign, left_comp]
  rcases hp with hp | hp <;> simp [mode, inside, hp]

private theorem neg_one_zpow_cutoff (H : ℕ) :
    (-1 : ℂ) ^ (H : ℤ) = -(-1 : ℂ) ^ ((H : ℤ) - 1) := by
  rw [show (H : ℤ) = (H : ℤ) - 1 + 1 by omega, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp

private theorem signed_high_of_positive {a r : ℕ}
    (ha : a + 3 ≤ 4) (hr : r + 1 < 3) (hp : a + r = 0 ∨ a + r = 2)
    {N : ℤ} {H : ℕ} {v w : degreeLE 4 D}
    (hv : left (compactRotation 1 Real.pi) v = (-1 : ℂ) ^ (H : ℤ) • v)
    (hw : left (compactRotation 1 Real.pi) w = (-1 : ℂ) ^ ((H : ℤ) - 1) • w)
    (hpos : ∀ j : ℤ, N ≤ j → projection ha hr j w = projection ha hr j v) :
    ∀ j : ℤ, N ≤ |j| → projection ha hr j w = modeSign j • projection ha hr j v := by
  intro j hj
  by_cases h : 0 ≤ j
  · rw [modeSign, ite_eq_left h, one_smul]
    exact hpos j (by simpa only [abs_of_nonneg h] using hj)
  · have hneg := lt_of_not_ge h
    have hhigh : N ≤ -j := by simpa only [abs_of_neg hneg] using hj
    let R := compactRotation (n := 4) 1 Real.pi
    have hrev (u : degreeLE 4 D) :
        projection ha hr (-j) (left R u) = left R (projection ha hr j u) := by
      simpa only [neg_neg] using projection_halfturn ha hr hp (-j) u
    apply left_injective R
    rw [modeSign, ite_eq_right h, map_smul, ← hrev w, ← hrev v,
      hw, hv, map_smul, map_smul, hpos (-j) hhigh, smul_smul]
    congr 1
    rw [neg_one_zpow_cutoff]
    ring

private theorem mode_abs (p : ℕ) (i : Fin n) (j : ℤ) : |mode p i j| = |j| := by
  by_cases h : inside p i <;> simp [mode, h]

private theorem modeSign_neg {j : ℤ} (h : j ≠ 0) : modeSign (-j) = -modeSign j := by
  by_cases hj : 0 ≤ j
  · have hn : ¬ 0 ≤ -j := by omega
    simp only [modeSign, hj, hn, ↓reduceIte]
  · have hn : 0 ≤ -j := by omega
    simp only [modeSign, hj, hn, ↓reduceIte, neg_neg]

private theorem signReflection_comm (i j : Fin n) :
    signReflection n i * signReflection n j = signReflection n j * signReflection n i := by
  apply Subtype.ext
  change (Matrix.diagonal _ : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal _ =
    Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext z
  exact mul_comm _ _

private theorem reflect_lift_high (ha : a + 3 ≤ n) {r : ℕ} (hr : r + 1 < 3)
    {N : ℤ} (hN : 0 < N) {v w : degreeLE n D} {ε τ : Fin n → ℂ}
    (hε : ∀ i, left (signReflection n i) v = ε i • v)
    (hτ : ∀ i, τ i = if inside (a + r) i then -ε i else ε i)
    (hmatch : ∀ j : ℤ, N ≤ |j| → projection ha hr j w = modeSign j • projection ha hr j v)
    (i : Fin n) (j : ℤ) (hj : N ≤ |j|) :
    projection ha hr j (left (signReflection n i) w) = τ i • projection ha hr j w := by
  have he := projection_left_sign ha hr i j v
  rw [hε i, map_smul] at he
  rw [projection_left_sign, hmatch _ (by simpa only [mode_abs] using hj), map_smul, ← he,
    smul_smul, hmatch j hj, smul_smul, hτ i]
  congr 1
  by_cases hi : inside (a + r) i
  · have hne : j ≠ 0 := by
      intro h
      rw [h, abs_zero] at hj
      omega
    simp only [mode, hi, ↓reduceIte, modeSign_neg hne]
    ring
  · simp only [mode, hi, ↓reduceIte, mul_comm]

private theorem project_signs (ha : a + 3 ≤ n) {r s : ℕ}
    (hr : r + 1 < 3) (hs : s + 1 < 3) {N : ℤ} (hN : 0 < N) {H : ℕ}
    {v w : degreeLE n D} {ε τ : Fin n → ℂ}
    (hε : ∀ i, left (signReflection n i) v = ε i • v)
    (hτ : ∀ i, τ i = if inside (a + r) i then -ε i else ε i)
    (hsq : ∀ i, τ i * τ i = 1)
    (hw : aeval (-I • generator ha hs) (tailPolynomial H) w = 0)
    (hmatch : ∀ j : ℤ, N ≤ |j| → projection ha hr j w = modeSign j • projection ha hr j v) :
    ∃ y : degreeLE n D, aeval (-I • generator ha hs) (tailPolynomial H) y = 0 ∧
      (∀ j : ℤ, N ≤ |j| → projection ha hr j y = modeSign j • projection ha hr j v) ∧
      ∀ i, left (signReflection n i) y = τ i • y := by
  classical
  let P := aeval (-I • generator (D := D) ha hs) (tailPolynomial H)
  have h (S : Finset (Fin n)) :
      ∃ y : degreeLE n D, P y = 0 ∧
        (∀ j : ℤ, N ≤ |j| → projection ha hr j y = modeSign j • projection ha hr j v) ∧
        ∀ i ∈ S, left (signReflection n i) y = τ i • y := by
    induction S using Finset.induction_on with
    | empty => exact ⟨w, hw, hmatch, by simp⟩
    | insert i S _ ih =>
      obtain ⟨y, hy, hyh, hys⟩ := ih
      let z := (1 / 2 : ℂ) • (y + τ i • left (signReflection n i) y)
      refine ⟨z, ?_, ?_, ?_⟩
      · have hker : P (left (signReflection n i) y) = 0 := kernel_left_sign ha hs hy i
        dsimp only [z]
        rw [map_smul, map_add, map_smul, hy, hker, smul_zero, add_zero, smul_zero]
      · intro j hj
        calc
          projection ha hr j z = projection ha hr j y := by
            dsimp only [z]
            rw [map_smul, map_add, map_smul, reflect_lift_high ha hr hN hε hτ hyh i j hj,
              smul_smul, hsq i, one_smul]
            module
          _ = _ := hyh j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with h | hj
        · subst j
          dsimp only [z]
          rw [map_smul, map_add, map_smul, left_comp, signReflection_mul_self, left_one]
          calc
            _ = (1 / 2 : ℂ) • (τ i • (y + τ i • left (signReflection n i) y)) := by
              have heq : τ i • (y + τ i • left (signReflection n i) y) =
                  τ i • y + left (signReflection n i) y := by
                rw [smul_add, smul_smul, hsq i, one_smul]
              rw [heq]
              module
            _ = _ := by rw [smul_comm]
        · have hc : left (signReflection n j) (left (signReflection n i) y) =
              left (signReflection n i) (left (signReflection n j) y) := by
            rw [left_comp, left_comp, signReflection_comm i j]
          dsimp only [z]
          rw [map_smul, map_add, map_smul, hc, hys j hj, map_smul]
          module
  obtain ⟨y, hy, hyh, hys⟩ := h Finset.univ
  exact ⟨y, hy, hyh, fun i => hys i (Finset.mem_univ i)⟩

/-- Apply the one-sided lift in the compact degree layer and project it to
the character obtained by changing both signs on the primary pair. -/
theorem exists_with_signs {a r s : ℕ} (ha : a + 3 ≤ 4)
    (hrs : r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0) (hr : r + 1 < 3) (hs : s + 1 < 3)
    (houter : a + r = 0 ∨ a + r = 2) (hmiddle : a + s = 1)
    {N : ℤ} (hN : 0 < N) (H : ℕ) (v : degreeLE 4 D) {ε τ : Fin 4 → ℂ}
    (hε : ∀ i, left (signReflection 4 i) v = ε i • v)
    (hτ : ∀ i, τ i = if inside (a + r) i then -ε i else ε i)
    (hsq : ∀ i, τ i * τ i = 1)
    (hhalf : left (compactRotation 1 Real.pi) v = (-1 : ℂ) ^ (H : ℤ) • v)
    (hv : ∀ j : ℤ, N + H ≤ j →
      projection ha hr j (aeval (-I • generator ha hs) (tailPolynomial H) v) = 0) :
    ∃ w : degreeLE 4 D, aeval (-I • generator ha hs) (tailPolynomial H) w = 0 ∧
      (∀ j : ℤ, N ≤ |j| → projection ha hr j w = modeSign j • projection ha hr j v) ∧
      ∀ i, left (signReflection 4 i) w = τ i • w := by
  obtain ⟨w, hw, hpos⟩ := RealAmbientAdjacentLifting.exists_lift ha hrs hr hs hN H v hv
  have hπ := kernel_eigen_pi ha hs hw
  rw [hmiddle] at hπ
  exact project_signs ha hr hs hN hε hτ hsq hw (signed_high_of_positive ha hr houter hhalf hπ hpos)

open Langlands.LocalFactor.Archimedean RealStandardFiltration
  RealStrictCharacterLanglandsQuotient PrincipalSeriesExtension GramFormula

private theorem exists_degree {ds : List RealBlock} (f : KF n ds) :
    ∃ D, restrictLinear n (f : G n → ℂ) ∈ degreeLE n D := by
  have hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
      Whittaker.rightTranslation ℂ (G n) (k : G n) (f : G n → ℂ))) := f.2.2
  have hle : OrthogonalFinitePolynomial.translateSpan (restrictLinear n f) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
        Whittaker.rightTranslation ℂ (G n) (k : G n) (f : G n → ℂ))).map (restrictLinear n) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨⟨Unitary.toUnits k, k.property⟩, rfl⟩, ?_⟩
    funext x
    show (f : G n → ℂ) (Unitary.toUnits x * Unitary.toUnits k) =
      (f : G n → ℂ) (Unitary.toUnits (x * k))
    rw [map_mul]
  have : FiniteDimensional ℂ (OrthogonalFinitePolynomial.translateSpan (restrictLinear n f)) :=
    Submodule.finiteDimensional_of_le hle
  exact RealKTypeCount.exists_mem_degreeLE
    (OrthogonalFinitePolynomial.mem_polynomialFunctions_of_finiteDimensional
      ((continuous_coe f).comp continuous_unitary_toUnits))

private theorem degreeLE_polynomial (n D : ℕ) :
    degreeLE n D ≤ (OrthogonalFinitePolynomial.polynomialFunctions n).toSubmodule := by
  let P := OrthogonalFinitePolynomial.polynomialFunctions n
  have h₁ : linearSpan n ≤ P.toSubmodule := by
    refine sup_le (Submodule.one_le.mpr (Subalgebra.one_mem P)) (Submodule.span_le.mpr ?_)
    rintro _ ⟨ij, rfl⟩
    exact OrthogonalFinitePolynomial.entry_mem_polynomialFunctions ij
  induction D with
  | zero =>
    rw [degreeLE, pow_zero]
    exact Submodule.one_le.mpr (Subalgebra.one_mem P)
  | succ D ih =>
    rw [degreeLE, pow_succ]
    exact Submodule.mul_le.mpr fun x hx y hy => P.mul_mem (ih hx) (h₁ hy)

private theorem continuous_degree (v : degreeLE n D) : Continuous (v : K n → ℂ) := by
  obtain ⟨P, hP⟩ := OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_polynomialFunctions
    (degreeLE_polynomial n D v.property)
  rw [funext hP]
  exact (MvPolynomial.continuous_eval P).comp (continuous_pi fun ij =>
    Complex.continuous_ofReal.comp (continuous_subtype_val.matrix_elem ij.1 ij.2))

private theorem right_finite_degree (v : degreeLE n D) :
    FiniteDimensional ℂ (OrthogonalFinitePolynomial.translateSpan (v : K n → ℂ)) := by
  apply Submodule.finiteDimensional_of_le (S₂ := degreeLE n D)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact right_mem_degreeLE v.property k

/-- Lift within the actual character module whose two primary endpoint signs
are changed. The signed high window and low middle window are stated using
the actual block Fourier coefficients. -/
theorem exists_character_lift {a r s : ℕ} (ha : a + 3 ≤ 4)
    (hrs : r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0) (hr : r + 1 < 3) (hs : s + 1 < 3)
    (houter : a + r = 0 ∨ a + r = 2) (hmiddle : a + s = 1)
    {N : ℤ} (hN : 0 < N) (H : ℕ) {ds es gs : List RealBlock} (hes : IsCharacterList es)
    (f : KF 4 ds) (g : KF 4 gs)
    (hτ : ∀ i : Fin 4, realPositionCharacter es i (-1) =
      if inside (a + r) i then -realPositionCharacter ds i (-1) else realPositionCharacter ds i (-1))
    (hhalf : (-1 : ℂ) ^ (H : ℤ) = realPositionCharacter ds 1 (-1) * realPositionCharacter ds 2 (-1))
    (hfg : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 4, Φ 4 1 j g x =
      (tailPolynomial H).eval (j : ℂ) * Φ 4 1 j f x)
    (hg : ∀ j : ℤ, N + H ≤ j → ∀ x ∈ unitaryCompact ℝ 4, Φ 4 (a + r) j g x = 0) :
    ∃ w : KF 4 es,
      (∀ j : ℤ, (H : ℤ) ≤ |j| → ∀ x ∈ unitaryCompact ℝ 4, Φ 4 1 j w x = 0) ∧
      (∀ j : ℤ, N ≤ |j| → ∀ x ∈ unitaryCompact ℝ 4, Φ 4 (a + r) j w x =
        modeSign j * Φ 4 (a + r) j f x) := by
  obtain ⟨Df, hf⟩ := exists_degree f
  obtain ⟨Dg, hg'⟩ := exists_degree g
  let D := max Df Dg
  let v : degreeLE 4 D := ⟨restrictLinear 4 f, degreeLE_mono (le_max_left Df Dg) hf⟩
  let u : degreeLE 4 D := ⟨restrictLinear 4 g, degreeLE_mono (le_max_right Df Dg) hg'⟩
  let ε (i : Fin 4) := realPositionCharacter ds i (-1)
  let τ (i : Fin 4) := realPositionCharacter es i (-1)
  have heval : aeval (-I • generator ha hs) (tailPolynomial H) v = u :=
    aeval_of_coeff ha hs (tailPolynomial H) f g v.property u.property
      (by simpa only [hmiddle] using hfg)
  have hhigh (j : ℤ) (hj : N + H ≤ j) :
      projection ha hr j (aeval (-I • generator ha hs) (tailPolynomial H) v) = 0 := by
    rw [heval]
    apply Subtype.ext
    funext x
    change (projection ha hr j (⟨restrictLinear 4 g, u.property⟩ : degreeLE 4 D) : K 4 → ℂ) x = 0
    rw [projection_apply_restrict, hg j hj _ x.property, mul_zero]
  have hsign (i : Fin 4) : left (signReflection 4 i) v = ε i • v := by
    apply Subtype.ext
    funext x
    change (f : G 4 → ℂ) (Unitary.toUnits (signReflection 4 i * x)) =
      ε i * (f : G 4 → ℂ) (Unitary.toUnits x)
    rw [map_mul]
    exact apply_signReflection_mul (realPositionCharacter_one ds) f.2.1.1 i _
  have ht : left (compactRotation 1 Real.pi) v = (-1 : ℂ) ^ (H : ℤ) • v := by
    rw [show compactRotation (n := 4) 1 Real.pi = signReflection 4 1 * signReflection 4 2 from
      compactRotation_pi (p := 1) (by decide), ← left_comp,
      hsign, map_smul, hsign, smul_smul, hhalf]
    rfl
  have hsq (i : Fin 4) : τ i * τ i = 1 := by
    rcases realPositionCharacter_neg_one es i with h | h <;> simp [τ, h]
  obtain ⟨w, hw, hwh, hws⟩ := exists_with_signs ha hrs hr hs houter hmiddle hN H v hsign hτ hsq ht hhigh
  let F := extension (shiftedExponent 4 (realPositionExponent es)) (w : K 4 → ℂ)
  have hF : F ∈ KF 4 es := by
    rw [KF, realStandardModule_eq hes]
    apply extension_mem_kFiniteFunctions _ (isSignedPower es).eq (continuous_degree w)
      (right_finite_degree w)
    apply RealLeviModes.apply_signDiagonal_mul (realPositionCharacter_one es)
    intro i x
    exact congrArg (fun z : degreeLE 4 D => (z : K 4 → ℂ) x) (hws i)
  let W : KF 4 es := ⟨F, hF⟩
  have hrestrict : restrictLinear 4 (W : G 4 → ℂ) = (w : K 4 → ℂ) :=
    funext (extension_unitary _ _)
  have hcoeff (p : ℕ) (j : ℤ) (x : G 4) (hx : x ∈ unitaryCompact ℝ 4) :
      compactCoeff p j w (⟨(x : Matrix (Fin 4) (Fin 4) ℝ), hx⟩ : K 4) = Φ 4 p j W x := by
    rw [← hrestrict, compactCoeff_restrict, toUnits_mk hx]
  refine ⟨W, ?_, ?_⟩
  · intro j hj x hx
    let κ : K 4 := ⟨(x : Matrix (Fin 4) (Fin 4) ℝ), hx⟩
    have h := congrArg (fun z : degreeLE 4 D => (z : K 4 → ℂ) κ) (kernel_low ha hs hw hj)
    change (projection ha hs j w : K 4 → ℂ) κ = 0 at h
    rw [projection_apply, hmiddle, hcoeff 1 j x hx] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero RealOrthogonalUncertainty.two_pi_ne_zero)
  · intro j hj x hx
    let κ : K 4 := ⟨(x : Matrix (Fin 4) (Fin 4) ℝ), hx⟩
    have h := congrArg (fun z : degreeLE 4 D => (z : K 4 → ℂ) κ) (hwh j hj)
    change (projection ha hr j w : K 4 → ℂ) κ =
      modeSign j * (projection ha hr j (⟨restrictLinear 4 f, v.property⟩ : degreeLE 4 D) : K 4 → ℂ) κ at h
    rw [projection_apply, hcoeff (a + r) j x hx, projection_apply_restrict, toUnits_mk hx] at h
    apply mul_left_cancel₀ (inv_ne_zero RealOrthogonalUncertainty.two_pi_ne_zero)
    simpa only [mul_left_comm _ (modeSign j)] using h

end Langlands.Archimedean.RealCompactParityLifting

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealStandardFiltration RealBlockJacquet RealTailMultiplierPolynomial
  RealCompactParityLifting RealStrictCharacterLanglandsQuotient
open RealInducedPairPositiveGenericMiddle (modeSign)

/-- One-sided lifting to the actual character presentation with the two
primary signs changed. -/
def RealCompactParityLiftingStatement : Prop :=
  ∀ (a r s : ℕ), a + 3 ≤ 4 →
    (r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0) → r + 1 < 3 → s + 1 < 3 →
    (a + r = 0 ∨ a + r = 2) → a + s = 1 →
    ∀ (N : ℤ), 0 < N → ∀ (H : ℕ) (ds es gs : List RealBlock), IsCharacterList es →
    ∀ (f : KF 4 ds) (g : KF 4 gs),
    (∀ i : Fin 4, realPositionCharacter es i (-1) =
      if inside (a + r) i then -realPositionCharacter ds i (-1) else realPositionCharacter ds i (-1)) →
    ((-1 : ℂ) ^ (H : ℤ) = realPositionCharacter ds 1 (-1) * realPositionCharacter ds 2 (-1)) →
    (∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 4,
      blockFourierCoefficient 4 1 j g x =
        (tailPolynomial H).eval (j : ℂ) * blockFourierCoefficient 4 1 j f x) →
    (∀ j : ℤ, N + H ≤ j → ∀ x ∈ unitaryCompact ℝ 4, blockFourierCoefficient 4 (a + r) j g x = 0) →
    ∃ w : KF 4 es,
      (∀ j : ℤ, (H : ℤ) ≤ |j| → ∀ x ∈ unitaryCompact ℝ 4, blockFourierCoefficient 4 1 j w x = 0) ∧
      (∀ j : ℤ, N ≤ |j| → ∀ x ∈ unitaryCompact ℝ 4,
        blockFourierCoefficient 4 (a + r) j w x = modeSign j * blockFourierCoefficient 4 (a + r) j f x)

theorem realCompactParityLifting : RealCompactParityLiftingStatement :=
  fun _ _ _ ha hrs hr hs houter hmiddle _ hN H _ _ _ hes f g =>
    exists_character_lift ha hrs hr hs houter hmiddle hN H hes f g

end Langlands.Archimedean
