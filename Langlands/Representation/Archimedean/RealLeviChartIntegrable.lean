import Langlands.Representation.Archimedean.RealLeviChartGram
import Langlands.Representation.Archimedean.RealLeviChartIntegralStatement
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Instances.Matrix

/-!
# Integrability of the Gram bound on the opposite unipotent radical of a parabolic subgroup

This module proves `RealLeviChartIntegrableStatement` (`realLeviChartIntegrable`).

The statement is proved for a general monotone block function `cl : Fin N → ι` (`gen`), by
strong induction on `N`. Let the first block have size `a` and write `N = a + M`. The
coordinates of the opposite unipotent radical split into the coordinates `X'` of the smaller
chart (`clR cl`) and the `a × M` entries `V` below the first block (`toCoord`, `embed`), and
`n̄(X) = [[1, 0], [V, B]]` with `B = n̄(X')` (`lowerC_embed`). Writing `B = T κ` with `T` upper
triangular and `κ` orthogonal, the substitution `V_k ↦ T V_k` (which has Jacobian `1`) separates
the integrand into a function of `V` alone (`Kf`) times the integrand of the smaller chart
(`peel_le`). The integral of `Kf` is finite by a column peel (`Kf_succ_le`, `Kf_lt_top`): the last
column `u` is substituted by `u = T' y` with `1 + ∑_{k} V_k V_kᵀ = T' T'ᵀ`, which reduces the
`u`-integral to the constant `cInt M β` (`lintegral_tm_le`). That constant is finite by peeling
one coordinate at a time with the one-dimensional scaling identity (`cInt_succ_le`,
`cInt_lt_top`). Only upper bounds of lower Lebesgue integrals are used, so no measurability
of the integrands is needed until the final step.
-/

noncomputable section

open MeasureTheory Matrix

namespace Langlands.Archimedean

set_option autoImplicit false

namespace RealLeviChartIntegrable

open GramFormula RealLeviChartGram

/-! ## Changes of variables -/

section Measure

/-- `∫⁻ f ∂ν ≤ ∫⁻ f ∘ g ∂μ` for a measure preserving `g`. -/
theorem lintegral_le_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {g : α → β} (hg : MeasurePreserving g μ ν)
    (f : β → ENNReal) : ∫⁻ b, f b ∂ν ≤ ∫⁻ a, f (g a) ∂μ := by
  rw [← hg.map_eq]
  exact lintegral_map_le f hg.measurable.aemeasurable

theorem volume_univ_of_isEmpty (κ X : Type*) [Fintype κ] [IsEmpty κ] [MeasureSpace X]
    [SigmaFinite (volume : Measure X)] : (volume : Measure (κ → X)) Set.univ = 1 := by
  rw [volume_pi, Measure.pi_univ, Finset.univ_eq_empty, Finset.prod_empty]

/-- Currying `(κ₁ × κ₂ → ℝ) → (κ₁ → κ₂ → ℝ)` preserves Lebesgue measure. -/
theorem measurePreserving_curry (κ₁ κ₂ : Type*) [Fintype κ₁] [Fintype κ₂] :
    MeasurePreserving (MeasurableEquiv.curry κ₁ κ₂ ℝ) volume volume := by
  refine ⟨(MeasurableEquiv.curry κ₁ κ₂ ℝ).measurable, ?_⟩
  symm
  show Measure.pi (fun _ => volume) = _
  refine Measure.pi_eq_generateFrom (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => MeasureTheory.Measure.FiniteSpanningSetsIn.pi fun _ => (volume : Measure ℝ).toFiniteSpanningSetsIn) ?_
  intro s hs
  choose t _ hst using hs
  have hs' : s = fun i => Set.univ.pi (t i) := funext fun i => (hst i).symm
  subst hs'
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.curry κ₁ κ₂ ℝ) ⁻¹' Set.univ.pi (fun i => Set.univ.pi (t i)) =
      Set.univ.pi (fun p : κ₁ × κ₂ => t p.1 p.2) := by
    ext w
    simp [Set.mem_pi, MeasurableEquiv.coe_curry, Prod.forall]
  rw [hpre, volume_pi_pi, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun i _ => (Measure.pi_pi _ _).symm

/-- The linear change of variables `u = T y`, as an upper bound. -/
theorem lintegral_le_mulVec {M : ℕ} {T : Matrix (Fin M) (Fin M) ℝ} (hT : T.det ≠ 0)
    (f : (Fin M → ℝ) → ENNReal) :
    ∫⁻ u, f u ≤ ENNReal.ofReal |T.det| * ∫⁻ y, f (T *ᵥ y) := by
  have hle : ∫⁻ u, f u ∂(Measure.map (toLin' T) volume) ≤ ∫⁻ y, f (toLin' T y) :=
    lintegral_map_le f (toLin' T).continuous_of_finiteDimensional.measurable.aemeasurable
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hT, lintegral_smul_measure,
    smul_eq_mul] at hle
  simp only [toLin'_apply] at hle
  calc ∫⁻ u, f u = ENNReal.ofReal |T.det| * (ENNReal.ofReal |(T.det)⁻¹| * ∫⁻ u, f u) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hT,
          abs_one, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal |T.det| * ∫⁻ y, f (T *ᵥ y) := by gcongr

/-- `y ↦ T y` preserves Lebesgue measure when `|det T| = 1`. -/
theorem measurePreserving_mulVec {M : ℕ} {T : Matrix (Fin M) (Fin M) ℝ} (hT : |T.det| = 1) :
    MeasurePreserving (fun v : Fin M → ℝ => T *ᵥ v) volume volume := by
  have hdet : T.det ≠ 0 := by
    intro h
    rw [h, abs_zero] at hT
    exact zero_ne_one hT
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  rw [abs_inv, hT, inv_one, ENNReal.ofReal_one, one_smul] at h
  have hf : (⇑(toLin' T) : (Fin M → ℝ) → Fin M → ℝ) = fun v => T *ᵥ v :=
    funext fun v => toLin'_apply T v
  rw [hf] at h
  exact ⟨(continuous_const.matrix_mulVec continuous_id).measurable, h⟩

/-- The scaling `x = s t` on the line, as an upper bound. -/
theorem lintegral_le_mul_left {s : ℝ} (hs : s ≠ 0) (f : ℝ → ENNReal) :
    ∫⁻ x, f x ≤ ENNReal.ofReal |s| * ∫⁻ t, f (s * t) := by
  have hle : ∫⁻ x, f x ∂(Measure.map (s * ·) volume) ≤ ∫⁻ t, f (s * t) :=
    lintegral_map_le f (continuous_const.mul continuous_id).measurable.aemeasurable
  rw [Real.map_volume_mul_left hs, lintegral_smul_measure, smul_eq_mul] at hle
  calc ∫⁻ x, f x = ENNReal.ofReal |s| * (ENNReal.ofReal |s⁻¹| * ∫⁻ x, f x) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hs,
          abs_one, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal |s| * ∫⁻ t, f (s * t) := by gcongr

/-- `∫ (A + x²)^δ dx ≤ A^{δ + 1/2} ∫ (1 + t²)^δ dt` for `A > 0`. -/
theorem lintegral_add_sq_rpow_le {A : ℝ} (hA : 0 < A) (δ : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((A + x ^ 2) ^ δ) ≤
      ENNReal.ofReal (A ^ (δ + 1 / 2)) * ∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2) ^ δ) := by
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  refine (lintegral_le_mul_left hs.ne' _).trans_eq ?_
  have h : ∀ t : ℝ, ENNReal.ofReal ((A + (Real.sqrt A * t) ^ 2) ^ δ) =
      ENNReal.ofReal (A ^ δ) * ENNReal.ofReal ((1 + t ^ 2) ^ δ) := by
    intro t
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _), ← Real.mul_rpow hA.le (by positivity),
      mul_pow, Real.sq_sqrt hA.le, mul_one_add A (t ^ 2)]
  simp_rw [h]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos hs, Real.sqrt_eq_rpow, ← Real.rpow_add hA,
    add_comm (1 / 2 : ℝ) δ]

/-- `∫ (1 + t²)^δ dt < ∞` for `δ < -1/2`. -/
theorem lintegral_one_add_sq_rpow_lt_top {δ : ℝ} (hδ : δ < -(1 / 2)) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2) ^ δ) < ⊤ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := -2 * δ)
    (by rw [Module.finrank_self, Nat.cast_one]; linarith)
  have heq : (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(-2 * δ) / 2)) =
      fun t => (1 + t ^ 2) ^ δ := by
    funext t
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  rw [heq] at h
  exact h.lintegral_lt_top

end Measure

/-! ## The constant `cInt M β` -/

section Constant

/-- `1 + ∑_{p ≥ r} y_p²`. -/
def tail {M : ℕ} (r : ℕ) (y : Fin M → ℝ) : ℝ :=
  1 + ∑ p : Fin M, if r ≤ (p : ℕ) then y p ^ 2 else 0

theorem one_le_tail {M : ℕ} (r : ℕ) (y : Fin M → ℝ) : 1 ≤ tail r y := by
  rw [tail]
  have : 0 ≤ ∑ p : Fin M, (if r ≤ (p : ℕ) then y p ^ 2 else 0) :=
    Finset.sum_nonneg fun p _ => by split_ifs <;> positivity
  linarith

theorem tail_pos {M : ℕ} (r : ℕ) (y : Fin M → ℝ) : 0 < tail r y :=
  lt_of_lt_of_le one_pos (one_le_tail r y)

theorem tm_one_add_vecMulVec_eq_tail {M : ℕ} (r : ℕ) (y : Fin M → ℝ) :
    tm r (1 + vecMulVec y y) = tail r y :=
  tm_one_add_vecMulVec r y

theorem tail_cons_zero {M : ℕ} (x : ℝ) (z : Fin M → ℝ) :
    tail 0 (Fin.cons x z : Fin (M + 1) → ℝ) = tail 0 z + x ^ 2 := by
  simp only [tail, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_le, ite_true]
  ring

theorem tail_cons_succ {M : ℕ} (x : ℝ) (z : Fin M → ℝ) (r : ℕ) :
    tail (r + 1) (Fin.cons x z : Fin (M + 1) → ℝ) = tail r z := by
  simp [tail, Fin.sum_univ_succ]

/-- The constant `∫ ∏_r (1 + ∑_{p ≥ r} y_p²)^{β_r} dy` over `ℝ^M`. -/
def cInt (M : ℕ) (β : ℕ → ℝ) : ENNReal :=
  ∫⁻ y : Fin M → ℝ, ENNReal.ofReal (∏ r : Fin M, tail r y ^ β r)

/-- Moving an extra exponent `e` of `t 0` into the first factor of a product. -/
theorem prod_rpow_add_ite {M : ℕ} (t : ℕ → ℝ) (ht : ∀ r, 0 < t r) (ht0 : M = 0 → t 0 = 1)
    (b : ℕ → ℝ) (e : ℝ) :
    t 0 ^ e * ∏ r : Fin M, t r ^ b r =
      ∏ r : Fin M, t r ^ (b r + if (r : ℕ) = 0 then e else 0) := by
  cases M with
  | zero => simp [ht0 rfl]
  | succ M =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    have h0 : ((0 : Fin (M + 1)) : ℕ) = 0 := rfl
    simp only [h0, Fin.val_succ, ite_true, Nat.add_one_ne_zero, ite_false,
      add_zero]
    rw [Real.rpow_add (ht 0)]
    ring

theorem cInt_succ_le (M : ℕ) (β : ℕ → ℝ)
    (hC : ∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2) ^ β 0) ≠ ⊤) :
    cInt (M + 1) β ≤ (∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2) ^ β 0)) *
      cInt M (fun r => β (r + 1) + if r = 0 then β 0 + 1 / 2 else 0) := by
  have e : (fun p : (Fin M → ℝ) × ℝ => (Fin.cons p.2 p.1 : Fin (M + 1) → ℝ)) =
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => ℝ) 0).symm ∘ Prod.swap := by
    funext p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have hg : MeasurePreserving (fun p : (Fin M → ℝ) × ℝ => (Fin.cons p.2 p.1 : Fin (M + 1) → ℝ))
      volume volume := by
    rw [e]
    exact (MeasurePreserving.symm _
      (volume_preserving_piFinSuccAbove (fun _ : Fin (M + 1) => ℝ) 0)).comp
        Measure.measurePreserving_swap
  rw [cInt]
  refine (lintegral_le_comp hg _).trans ?_
  rw [Measure.volume_eq_prod]
  refine (lintegral_prod_le _).trans ?_
  rw [cInt, ← lintegral_const_mul' _ _ hC]
  refine lintegral_mono fun z => ?_
  have hA : 0 < tail 0 z := tail_pos 0 z
  have hprod : ∀ x : ℝ, ∏ r : Fin (M + 1), tail r (Fin.cons x z : Fin (M + 1) → ℝ) ^ β r =
      (tail 0 z + x ^ 2) ^ β 0 * ∏ r : Fin M, tail r z ^ β (r + 1) := by
    intro x
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, tail_cons_zero, tail_cons_succ]
  simp only [hprod]
  have hP : 0 ≤ ∏ r : Fin M, tail r z ^ β (r + 1) :=
    Finset.prod_nonneg fun r _ => Real.rpow_nonneg (tail_pos _ _).le _
  simp_rw [ENNReal.ofReal_mul' hP]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have h0 : M = 0 → tail 0 z = 1 := by
    intro hM
    subst hM
    simp [tail]
  have hshift := prod_rpow_add_ite (fun r => tail r z) (fun r => tail_pos r z) h0
    (fun r => β (r + 1)) (β 0 + 1 / 2)
  calc (∫⁻ x, ENNReal.ofReal ((tail 0 z + x ^ 2) ^ β 0)) *
        ENNReal.ofReal (∏ r : Fin M, tail r z ^ β (r + 1))
      ≤ (ENNReal.ofReal (tail 0 z ^ (β 0 + 1 / 2)) *
          ∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2) ^ β 0)) *
          ENNReal.ofReal (∏ r : Fin M, tail r z ^ β (r + 1)) := by
        gcongr
        exact lintegral_add_sq_rpow_le hA (β 0)
    _ = (∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2) ^ β 0)) *
          ENNReal.ofReal (∏ r : Fin M,
            tail r z ^ (β (r + 1) + if (r : ℕ) = 0 then β 0 + 1 / 2 else 0)) := by
        rw [← hshift, ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _)]
        ring

theorem cInt_lt_top : ∀ (M : ℕ) (β : ℕ → ℝ), (∀ r < M, β r ≤ -(1 / 2)) →
    (0 < M → β 0 < -(1 / 2)) → cInt M β < ⊤
  | 0, β, _, _ => by
    rw [cInt]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one, lintegral_one]
    rw [volume_univ_of_isEmpty]
    exact ENNReal.one_lt_top
  | M + 1, β, h1, h0 => by
    have hb0 : β 0 < -(1 / 2) := h0 (Nat.succ_pos M)
    have hC := lintegral_one_add_sq_rpow_lt_top hb0
    refine lt_of_le_of_lt (cInt_succ_le M β hC.ne) (ENNReal.mul_lt_top hC ?_)
    refine cInt_lt_top M _ (fun r hr => ?_) (fun hM => ?_)
    · have h2 := h1 (r + 1) (by omega)
      split_ifs <;> linarith
    · have h2 := h1 (0 + 1) (by omega)
      rw [ite_eq_left rfl]
      linarith

end Constant

/-! ## The column peel -/

section Columns

/-- The part of the integrand that depends on the entries `V` below the first block. -/
def Kf (a M : ℕ) (α β : ℕ → ℝ) (V : Fin a → Fin M → ℝ) : ℝ :=
  (∏ j : Fin a, (1 + colGram j V).det ^ α j) * ∏ r : Fin M, tm r (1 + colGram a V) ^ β r

/-- The integral over the last column, with `1 + G = T Tᵀ` and `u = T y`. -/
theorem lintegral_tm_le {M : ℕ} {G : Matrix (Fin M) (Fin M) ℝ} (hG : G.PosSemidef)
    (β : ℕ → ℝ) :
    ∫⁻ u : Fin M → ℝ, ENNReal.ofReal (∏ r : Fin M, tm r (1 + G + vecMulVec u u) ^ β r) ≤
      ENNReal.ofReal ((1 + G).det ^ (1 / 2 : ℝ) * ∏ r : Fin M, tm r (1 + G) ^ β r) *
        cInt M β := by
  have hL : (1 + G).PosDef := PosDef.one.add_posSemidef hG
  obtain ⟨T, hT, hTu, hTT⟩ := Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_conjTranspose hL
  rw [conjTranspose_eq_transpose_of_trivial] at hTT
  have hdetT : T.det ≠ 0 := ((isUnit_iff_isUnit_det T).mp hTu).ne_zero
  refine (lintegral_le_mulVec hdetT _).trans (le_of_eq ?_)
  have htm : ∀ r : ℕ, tm r (1 + G) = diagonalTail r T ^ 2 := by
    intro r
    have h := tm_conj hT r 1
    rwa [Matrix.mul_one, hTT, tm_one, mul_one] at h
  have key : ∀ y : Fin M → ℝ,
      ∏ r : Fin M, tm r (1 + G + vecMulVec (T *ᵥ y) (T *ᵥ y)) ^ β r =
        (∏ r : Fin M, tm r (1 + G) ^ β r) * ∏ r : Fin M, tail r y ^ β r := by
    intro y
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    have h1 : 1 + G + vecMulVec (T *ᵥ y) (T *ᵥ y) = T * (1 + vecMulVec y y) * Tᵀ := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hTT, mul_vecMulVec, vecMulVec_mul,
        vecMul_transpose]
    rw [h1, tm_conj hT, tm_one_add_vecMulVec_eq_tail, ← htm,
      Real.mul_rpow (tm_pos hG r).le (tail_pos r y).le]
  simp_rw [key]
  have hK : 0 ≤ ∏ r : Fin M, tm r (1 + G) ^ β r :=
    Finset.prod_nonneg fun r _ => Real.rpow_nonneg (tm_pos hG r).le _
  simp_rw [ENNReal.ofReal_mul hK]
  have hdet2 : (1 + G).det = T.det ^ 2 := by
    rw [← hTT, det_mul, det_transpose, sq]
  have habs : |T.det| = (1 + G).det ^ (1 / 2 : ℝ) := by
    rw [hdet2, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, cInt, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _), habs]

theorem Kf_succ_le (a' M : ℕ) (α β : ℕ → ℝ) (hc : cInt M β ≠ ⊤) :
    ∫⁻ V : Fin (a' + 1) → Fin M → ℝ, ENNReal.ofReal (Kf (a' + 1) M α β V) ≤
      cInt M β * ∫⁻ V : Fin a' → Fin M → ℝ,
        ENNReal.ofReal (Kf a' M α (fun r => β r + if r = 0 then α a' + 1 / 2 else 0) V) := by
  have e : (fun p : (Fin a' → Fin M → ℝ) × (Fin M → ℝ) =>
      (Fin.snoc p.1 p.2 : Fin (a' + 1) → Fin M → ℝ)) =
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (a' + 1) => Fin M → ℝ)
        (Fin.last a')).symm ∘ Prod.swap := by
    funext p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have hg : MeasurePreserving (fun p : (Fin a' → Fin M → ℝ) × (Fin M → ℝ) =>
      (Fin.snoc p.1 p.2 : Fin (a' + 1) → Fin M → ℝ)) volume volume := by
    rw [e]
    exact (MeasurePreserving.symm _
      (volume_preserving_piFinSuccAbove (fun _ : Fin (a' + 1) => Fin M → ℝ)
        (Fin.last a'))).comp Measure.measurePreserving_swap
  refine (lintegral_le_comp hg _).trans ?_
  rw [Measure.volume_eq_prod]
  refine (lintegral_prod_le _).trans ?_
  rw [← lintegral_const_mul' _ _ hc]
  refine lintegral_mono fun V' => ?_
  have hG := posSemidef_colGram a' V'
  have hsplit : ∀ u : Fin M → ℝ,
      Kf (a' + 1) M α β (Fin.snoc V' u : Fin (a' + 1) → Fin M → ℝ) =
        ((∏ j : Fin a', (1 + colGram j V').det ^ α j) * (1 + colGram a' V').det ^ α a') *
          ∏ r : Fin M, tm r (1 + colGram a' V' + vecMulVec u u) ^ β r := by
    intro u
    rw [Kf, Fin.prod_univ_castSucc, colGram_snoc_succ,
      ← add_assoc (1 : Matrix (Fin M) (Fin M) ℝ)]
    congr 2
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [Fin.val_castSucc, colGram_snoc_of_le V' u j.2.le]
    · rw [Fin.val_last, colGram_snoc_of_le V' u le_rfl]
  simp only [hsplit]
  have hP : 0 ≤ (∏ j : Fin a', (1 + colGram j V').det ^ α j) *
      (1 + colGram a' V').det ^ α a' :=
    mul_nonneg (Finset.prod_nonneg fun j _ =>
      Real.rpow_nonneg (det_one_add_pos (posSemidef_colGram _ _)).le _)
      (Real.rpow_nonneg (det_one_add_pos hG).le _)
  simp_rw [ENNReal.ofReal_mul hP]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h0 : M = 0 → tm 0 (1 + colGram a' V') = 1 := by
    intro hM
    subst hM
    rw [tm_zero]
    exact det_isEmpty
  have hshift := prod_rpow_add_ite (fun r => tm r (1 + colGram a' V')) (fun r => tm_pos hG r) h0
    β (α a' + 1 / 2)
  calc ENNReal.ofReal ((∏ j : Fin a', (1 + colGram j V').det ^ α j) *
          (1 + colGram a' V').det ^ α a') *
        ∫⁻ u, ENNReal.ofReal (∏ r : Fin M, tm r (1 + colGram a' V' + vecMulVec u u) ^ β r)
      ≤ ENNReal.ofReal ((∏ j : Fin a', (1 + colGram j V').det ^ α j) *
          (1 + colGram a' V').det ^ α a') *
        (ENNReal.ofReal ((1 + colGram a' V').det ^ (1 / 2 : ℝ) *
          ∏ r : Fin M, tm r (1 + colGram a' V') ^ β r) * cInt M β) := by
        gcongr
        exact lintegral_tm_le hG β
    _ = cInt M β * ENNReal.ofReal (Kf a' M α
          (fun r => β r + if r = 0 then α a' + 1 / 2 else 0) V') := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hP, mul_comm _ (cInt M β)]
        congr 2
        simp only [Kf]
        rw [← hshift, tm_zero, Real.rpow_add (det_one_add_pos hG)]
        ring

theorem Kf_lt_top : ∀ (a M : ℕ) (α β : ℕ → ℝ), (∀ j < a, 0 < j → α j ≤ -(1 / 2)) →
    (0 < a → ∀ r < M, β r ≤ -(1 / 2)) → (0 < a → 0 < M → β 0 < -(1 / 2)) →
    ∫⁻ V : Fin a → Fin M → ℝ, ENNReal.ofReal (Kf a M α β V) < ⊤
  | 0, M, α, β, _, _, _ => by
    have h : ∀ V : Fin 0 → Fin M → ℝ, Kf 0 M α β V = 1 := by
      intro V
      have h0 : colGram 0 V = 0 := by simp [colGram]
      simp [Kf, h0, tm_one]
    simp only [h, ENNReal.ofReal_one, lintegral_one]
    rw [volume_univ_of_isEmpty]
    exact ENNReal.one_lt_top
  | a' + 1, M, α, β, hα, hβ, hβ0 => by
    have hc : cInt M β < ⊤ := cInt_lt_top M β (hβ (Nat.succ_pos a')) (hβ0 (Nat.succ_pos a'))
    refine lt_of_le_of_lt (Kf_succ_le a' M α β hc.ne) (ENNReal.mul_lt_top hc ?_)
    have hlast : 0 < a' → α a' ≤ -(1 / 2) := fun h => hα a' (Nat.lt_succ_self a') h
    refine Kf_lt_top a' M α _ (fun j hj hj0 => hα j (by omega) hj0) (fun ha' r hr => ?_)
      (fun ha' hM => ?_)
    · have h1 := hβ (Nat.succ_pos a') r hr
      have h2 := hlast ha'
      split_ifs <;> linarith
    · have h1 := hβ0 (Nat.succ_pos a') hM
      have h2 := hlast ha'
      rw [ite_eq_left rfl]
      linarith

end Columns

/-! ## Charts for a general monotone block function -/

section Chart

variable {ι : Type*} [LinearOrder ι]

/-- The coordinates `X_{pq}`, `cl q < cl p`, of the opposite unipotent radical. -/
abbrev CoordC {N : ℕ} (cl : Fin N → ι) := {pq : Fin N × Fin N // cl pq.2 < cl pq.1}

/-- `n̄(X)`: the identity matrix with the entries `X_{pq}` at the coordinates. -/
def lowerC {N : ℕ} (cl : Fin N → ι) (X : CoordC cl → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun p q => if h : cl q < cl p then X ⟨(p, q), h⟩ else if p = q then 1 else 0

variable {N : ℕ} {cl : Fin N → ι}

theorem lowerC_isLowerTriangular (hcl : Monotone cl) (X : CoordC cl → ℝ) :
    (lowerC cl X).IsLowerTriangular := by
  intro p q hpq
  have hpq' : p < q := hpq
  have h1 : ¬ cl q < cl p := not_lt.mpr (hcl hpq'.le)
  simp [lowerC, h1, hpq'.ne]

theorem det_lowerC (hcl : Monotone cl) (X : CoordC cl → ℝ) : (lowerC cl X).det = 1 := by
  rw [det_of_isLowerTriangular _ (lowerC_isLowerTriangular hcl X)]
  refine Finset.prod_eq_one fun p _ => ?_
  simp [lowerC]

theorem isUnit_lowerC (hcl : Monotone cl) (X : CoordC cl → ℝ) : IsUnit (lowerC cl X) :=
  (isUnit_iff_isUnit_det _).mpr (by rw [det_lowerC hcl]; exact isUnit_one)

theorem gram_lowerC_pos (hcl : Monotone cl) (X : CoordC cl → ℝ) (l : ℕ) :
    0 < gram l (lowerC cl X) := by
  have h := gram_pos (isUnit_lowerC hcl X).unit l
  rwa [IsUnit.unit_spec] at h

theorem continuous_lowerC : Continuous (lowerC cl) := by
  refine continuous_matrix fun p q => ?_
  simp only [lowerC, of_apply]
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const
  · exact continuous_const

theorem continuous_gram (l : ℕ) {n : ℕ} :
    Continuous fun x : Matrix (Fin n) (Fin n) ℝ => gram l x := by
  have h : Continuous fun x : Matrix (Fin n) (Fin n) ℝ => paddedGram l x := by
    refine continuous_matrix fun p q => ?_
    simp only [paddedGram, of_apply]
    split_ifs
    · exact (continuous_id.matrix_mul continuous_id.matrix_transpose).matrix_elem p q
    · exact continuous_const
  exact h.matrix_det

theorem continuous_prod_gram (hcl : Monotone cl) (e : Fin N → ℝ) :
    Continuous fun X : CoordC cl → ℝ => ∏ l : Fin N, gram l (lowerC cl X) ^ e l :=
  continuous_finsetProd _ fun l _ => ((continuous_gram l).comp continuous_lowerC).rpow_const
    fun X => Or.inl (gram_lowerC_pos hcl X l).ne'

end Chart

/-! ## The first-block peel -/

section Peel

variable {ι : Type*} [LinearOrder ι] {a M : ℕ} {cl : Fin (a + M) → ι}

/-- The block function on the last `M` positions. -/
def clR (cl : Fin (a + M) → ι) : Fin M → ι := fun r => cl (Fin.natAdd a r)

/-- The coordinates of the smaller chart and the entries below the first block, as
coordinates of the chart of `cl`. -/
def toCoord (hfr : ∀ (j : Fin a) (r : Fin M), cl (Fin.castAdd M j) < cl (Fin.natAdd a r)) :
    CoordC (clR cl) ⊕ (Fin a × Fin M) → CoordC cl
  | .inl x => ⟨(Fin.natAdd a x.1.1, Fin.natAdd a x.1.2), x.2⟩
  | .inr jr => ⟨(Fin.natAdd a jr.2, Fin.castAdd M jr.1), hfr jr.1 jr.2⟩

theorem natAdd_ne_castAdd (r : Fin M) (j : Fin a) : Fin.natAdd a r ≠ Fin.castAdd M j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

theorem toCoord_bijective {c0 : ι} (h1 : ∀ j : Fin a, cl (Fin.castAdd M j) = c0)
    (h2 : ∀ r : Fin M, c0 < cl (Fin.natAdd a r))
    (hfr : ∀ (j : Fin a) (r : Fin M), cl (Fin.castAdd M j) < cl (Fin.natAdd a r)) :
    Function.Bijective (toCoord hfr) := by
  constructor
  · rintro (⟨⟨r, s⟩, hx⟩ | ⟨j, r⟩) (⟨⟨r', s'⟩, hy⟩ | ⟨j', r'⟩) h <;>
      replace h := congrArg Subtype.val h <;>
      simp only [toCoord, Prod.mk.injEq] at h
    · rw [Fin.natAdd_inj, Fin.natAdd_inj] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · exact absurd h.2 (natAdd_ne_castAdd _ _)
    · exact absurd h.2.symm (natAdd_ne_castAdd _ _)
    · rw [Fin.natAdd_inj, Fin.castAdd_inj] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  · rintro ⟨⟨p, q⟩, h⟩
    induction p using Fin.addCases with
    | left i =>
      exfalso
      induction q using Fin.addCases with
      | left j =>
        rw [h1, h1] at h
        exact lt_irrefl _ h
      | right s =>
        rw [h1] at h
        exact lt_asymm h (h2 s)
    | right r =>
      induction q using Fin.addCases with
      | left j => exact ⟨.inr (j, r), rfl⟩
      | right s => exact ⟨.inl ⟨(r, s), h⟩, rfl⟩

/-- `(X', V) ↦ X`: the coordinates of the smaller chart and the entries below the first block
put together. -/
def embed (e : CoordC (clR cl) ⊕ (Fin a × Fin M) ≃ CoordC cl)
    (p : (CoordC (clR cl) → ℝ) × (Fin a → Fin M → ℝ)) : CoordC cl → ℝ :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) e
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)).symm (p.1, Function.uncurry p.2))

theorem measurePreserving_embed (e : CoordC (clR cl) ⊕ (Fin a × Fin M) ≃ CoordC cl) :
    MeasurePreserving (embed e) volume volume := by
  have h1 := measurePreserving_piCongrLeft (fun _ : CoordC cl => (volume : Measure ℝ)) e
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : CoordC (clR cl) ⊕ (Fin a × Fin M) => ℝ)
  have h3 := (MeasurePreserving.id (volume : Measure (CoordC (clR cl) → ℝ))).prod
    (MeasurePreserving.symm _ (measurePreserving_curry (Fin a) (Fin M)))
  exact h1.comp (h2.comp h3)

theorem embed_inl (e : CoordC (clR cl) ⊕ (Fin a × Fin M) ≃ CoordC cl)
    (X' : CoordC (clR cl) → ℝ) (V : Fin a → Fin M → ℝ) (x : CoordC (clR cl)) :
    embed e (X', V) (e (.inl x)) = X' x := by
  rw [embed, MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

theorem embed_inr (e : CoordC (clR cl) ⊕ (Fin a × Fin M) ≃ CoordC cl)
    (X' : CoordC (clR cl) → ℝ) (V : Fin a → Fin M → ℝ) (j : Fin a) (r : Fin M) :
    embed e (X', V) (e (.inr (j, r))) = V j r := by
  rw [embed, MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

theorem blockLower_castAdd_castAdd (V : Fin a → Fin M → ℝ) (B : Matrix (Fin M) (Fin M) ℝ)
    (i j : Fin a) :
    blockLower V B (Fin.castAdd M i) (Fin.castAdd M j) = (1 : Matrix (Fin a) (Fin a) ℝ) i j := by
  simp [blockLower]

theorem blockLower_castAdd_natAdd (V : Fin a → Fin M → ℝ) (B : Matrix (Fin M) (Fin M) ℝ)
    (i : Fin a) (s : Fin M) : blockLower V B (Fin.castAdd M i) (Fin.natAdd a s) = 0 := by
  simp [blockLower]

theorem blockLower_natAdd_castAdd (V : Fin a → Fin M → ℝ) (B : Matrix (Fin M) (Fin M) ℝ)
    (r : Fin M) (j : Fin a) : blockLower V B (Fin.natAdd a r) (Fin.castAdd M j) = V j r := by
  simp [blockLower, colMat]

theorem blockLower_natAdd_natAdd (V : Fin a → Fin M → ℝ) (B : Matrix (Fin M) (Fin M) ℝ)
    (r s : Fin M) : blockLower V B (Fin.natAdd a r) (Fin.natAdd a s) = B r s := by
  simp [blockLower]

theorem lowerC_embed {c0 : ι} (h1 : ∀ j : Fin a, cl (Fin.castAdd M j) = c0)
    (h2 : ∀ r : Fin M, c0 < cl (Fin.natAdd a r))
    (hfr : ∀ (j : Fin a) (r : Fin M), cl (Fin.castAdd M j) < cl (Fin.natAdd a r))
    (X' : CoordC (clR cl) → ℝ) (V : Fin a → Fin M → ℝ) :
    lowerC cl (embed (Equiv.ofBijective _ (toCoord_bijective h1 h2 hfr)) (X', V)) =
      blockLower V (lowerC (clR cl) X') := by
  ext p q
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left j =>
      have hn : ¬ cl (Fin.castAdd M j) < cl (Fin.castAdd M i) := by
        rw [h1, h1]
        exact lt_irrefl _
      rw [lowerC, of_apply, dite_eq_right hn, blockLower_castAdd_castAdd]
      simp only [Fin.castAdd_inj, Matrix.one_apply]
    | right s =>
      have hn : ¬ cl (Fin.natAdd a s) < cl (Fin.castAdd M i) := by
        rw [h1]
        exact lt_asymm (h2 s)
      rw [lowerC, of_apply, dite_eq_right hn, blockLower_castAdd_natAdd,
        ite_eq_right (natAdd_ne_castAdd s i).symm]
  | right r =>
    induction q using Fin.addCases with
    | left j =>
      rw [lowerC, of_apply, dite_eq_left (hfr j r), blockLower_natAdd_castAdd]
      exact embed_inr _ X' V j r
    | right s =>
      rw [blockLower_natAdd_natAdd]
      by_cases hrs : cl (Fin.natAdd a s) < cl (Fin.natAdd a r)
      · rw [lowerC, of_apply, dite_eq_left hrs, lowerC, of_apply,
          dite_eq_left (show clR cl s < clR cl r from hrs)]
        exact embed_inl _ X' V ⟨(r, s), hrs⟩
      · rw [lowerC, of_apply, dite_eq_right hrs, lowerC, of_apply,
          dite_eq_right (show ¬ clR cl s < clR cl r from hrs)]
        simp only [Fin.natAdd_inj]

/-- **The first-block peel.** -/
theorem peel_le (hcl : Monotone cl) {c0 : ι} (h1 : ∀ j : Fin a, cl (Fin.castAdd M j) = c0)
    (h2 : ∀ r : Fin M, c0 < cl (Fin.natAdd a r)) (γ : ℕ → ℝ)
    (hK : ∫⁻ V : Fin a → Fin M → ℝ, ENNReal.ofReal (Kf a M γ (fun r => γ (a + r)) V) ≠ ⊤) :
    ∫⁻ X : CoordC cl → ℝ, ENNReal.ofReal (∏ l : Fin (a + M), gram l (lowerC cl X) ^ γ l) ≤
      (∫⁻ V : Fin a → Fin M → ℝ, ENNReal.ofReal (Kf a M γ (fun r => γ (a + r)) V)) *
        ∫⁻ X' : CoordC (clR cl) → ℝ,
          ENNReal.ofReal (∏ r : Fin M, gram r (lowerC (clR cl) X') ^ γ (a + r)) := by
  have hfr : ∀ (j : Fin a) (r : Fin M), cl (Fin.castAdd M j) < cl (Fin.natAdd a r) :=
    fun j r => by
      rw [h1]
      exact h2 r
  have hclR : Monotone (clR cl) := fun r s hrs => hcl (by
    rw [Fin.le_def] at hrs ⊢
    simp only [Fin.val_natAdd]
    omega)
  refine (lintegral_le_comp
    (measurePreserving_embed (Equiv.ofBijective _ (toCoord_bijective h1 h2 hfr))) _).trans ?_
  rw [Measure.volume_eq_prod]
  refine (lintegral_prod_le _).trans ?_
  rw [← lintegral_const_mul' _ _ hK]
  refine lintegral_mono fun X' => ?_
  simp only [lowerC_embed h1 h2 hfr]
  obtain ⟨T, κ, hT, -, hκ, hTκ⟩ :=
    Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary _ (isUnit_lowerC hclR X')
  have hκ' : κ * κᵀ = 1 := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hκ
    exact hκ
  have hκd : κ.det * κ.det = 1 := by
    have h := congrArg det hκ'
    rwa [det_mul, det_transpose, det_one] at h
  have hB1 := det_lowerC hclR X'
  rw [hTκ, det_mul] at hB1
  have hdet2 : T.det ^ 2 = 1 := by
    calc T.det ^ 2 = T.det ^ 2 * (κ.det * κ.det) := by rw [hκd, mul_one]
      _ = (T.det * κ.det) ^ 2 := by ring
      _ = 1 := by rw [hB1, one_pow]
  have habs : |T.det| = 1 := by
    rcases mul_self_eq_one_iff.mp (by rw [← sq]; exact hdet2 : T.det * T.det = 1) with h | h <;>
      simp [h]
  refine (lintegral_le_comp (measurePreserving_pi (fun _ => volume) (fun _ => volume)
    (fun _ : Fin a => measurePreserving_mulVec habs)) _).trans ?_
  have hgram : ∀ r : ℕ, 0 < gram r (T * κ) := fun r => hTκ ▸ gram_lowerC_pos hclR X' r
  have key : ∀ V : Fin a → Fin M → ℝ,
      ∏ l : Fin (a + M), gram l (blockLower (fun k => T *ᵥ V k) (lowerC (clR cl) X')) ^ γ l =
        Kf a M γ (fun r => γ (a + r)) V *
          ∏ r : Fin M, gram r (lowerC (clR cl) X') ^ γ (a + r) := by
    intro V
    rw [Fin.prod_univ_add, hTκ]
    simp only [Fin.val_castAdd, Fin.val_natAdd, Kf]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [gram_blockLower_conj_of_le hκ' hdet2 V j.2.le]
    · refine Finset.prod_congr rfl fun r _ => ?_
      rw [gram_blockLower_conj_add hT hκ' V r,
        Real.mul_rpow (hgram r).le (tm_pos (posSemidef_colGram a V) r).le]
      ring
  simp only [key]
  have hG0 : 0 ≤ ∏ r : Fin M, gram r (lowerC (clR cl) X') ^ γ (a + r) :=
    Finset.prod_nonneg fun r _ => Real.rpow_nonneg (gram_lowerC_pos hclR X' r).le _
  simp_rw [ENNReal.ofReal_mul' hG0]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  exact le_rfl

end Peel

/-! ## The induction over the blocks -/

section Induction

variable {ι : Type*} [LinearOrder ι]

theorem exists_first_block {N : ℕ} (cl : Fin N → ι) (hcl : Monotone cl) (hN : 0 < N) :
    ∃ a, 1 ≤ a ∧ a ≤ N ∧ (∀ p : Fin N, (p : ℕ) < a → cl p = cl ⟨0, hN⟩) ∧
      (∀ p : Fin N, a ≤ (p : ℕ) → cl ⟨0, hN⟩ < cl p) := by
  classical
  let P : ℕ → Prop := fun k => ∀ p : Fin N, (p : ℕ) < k → cl p = cl ⟨0, hN⟩
  have hP1 : P 1 := fun p hp => by
    have : p = ⟨0, hN⟩ := Fin.ext (by simp only; omega)
    rw [this]
  refine ⟨Nat.findGreatest P N, Nat.le_findGreatest hN hP1, Nat.findGreatest_le N,
    Nat.findGreatest_spec hN hP1, fun p hp => ?_⟩
  have hnot : ¬ ∀ q : Fin N, (q : ℕ) < Nat.findGreatest P N + 1 → cl q = cl ⟨0, hN⟩ :=
    Nat.findGreatest_is_greatest (P := P) (n := N) (Nat.lt_succ_self _) (by have := p.2; omega)
  push Not at hnot
  obtain ⟨q, hq, hne⟩ := hnot
  have hqa : (q : ℕ) = Nat.findGreatest P N := by
    by_contra hqa
    exact hne (Nat.findGreatest_spec hN hP1 q (by omega))
  have h0q : cl ⟨0, hN⟩ ≤ cl q := hcl (Fin.le_def.mpr (Nat.zero_le _))
  have hqp : cl q ≤ cl p := hcl (Fin.le_def.mpr (by omega))
  exact lt_of_lt_of_le (lt_of_le_of_ne h0q (Ne.symm hne)) hqp

/-- **Integrability of the Gram bound for a general monotone block function.** -/
theorem gen : ∀ (N : ℕ) (cl : Fin N → ι), Monotone cl → ∀ γ : ℕ → ℝ,
    (∀ l : Fin N, 0 < (l : ℕ) → γ l ≤ -(1 / 2)) →
    (∀ k l : Fin N, (k : ℕ) + 1 = l → cl k < cl l → γ l < -(1 / 2)) →
    ∫⁻ X : CoordC cl → ℝ, ENNReal.ofReal (∏ l : Fin N, gram l (lowerC cl X) ^ γ l) < ⊤ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro cl hcl γ hγ1 hγ2
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : IsEmpty (CoordC cl) := ⟨fun x => x.1.1.elim0⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty, ENNReal.ofReal_one, lintegral_one]
    rw [volume_univ_of_isEmpty]
    exact ENNReal.one_lt_top
  · obtain ⟨a, ha1, haN, hfirst, hrest⟩ := exists_first_block cl hcl hN
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le haN
    have h1 : ∀ j : Fin a, cl (Fin.castAdd M j) = cl ⟨0, hN⟩ := fun j => hfirst _ (by simp)
    have h2 : ∀ r : Fin M, cl ⟨0, hN⟩ < cl (Fin.natAdd a r) := fun r => hrest _ (by simp)
    have hK : ∫⁻ V : Fin a → Fin M → ℝ,
        ENNReal.ofReal (Kf a M γ (fun r => γ (a + r)) V) < ⊤ := by
      refine Kf_lt_top a M γ _ (fun j hj hj0 => hγ1 ⟨j, by omega⟩ hj0)
        (fun _ r hr => hγ1 ⟨a + r, by omega⟩ (by simp only; omega)) (fun _ hM => ?_)
      refine hγ2 ⟨a - 1, by omega⟩ ⟨a, by omega⟩ (by simp only; omega) ?_
      rw [hfirst _ (by simp only; omega)]
      exact hrest _ (by simp only; omega)
    have hclR : Monotone (clR cl) := fun r s hrs => hcl (by
      rw [Fin.le_def] at hrs ⊢
      simp only [Fin.val_natAdd]
      omega)
    have hG := ih M (by omega) (clR cl) hclR (fun r => γ (a + r))
      (fun l hl => hγ1 (Fin.natAdd a l) (by simp only [Fin.val_natAdd]; omega))
      (fun k l hkl h => hγ2 (Fin.natAdd a k) (Fin.natAdd a l)
        (by simp only [Fin.val_natAdd]; omega) h)
    exact lt_of_le_of_lt (peel_le hcl h1 h2 γ hK.ne) (ENNReal.mul_lt_top hK hG)

end Induction

end RealLeviChartIntegrable

open RealLeviChartIntegrable in
/-- **Integrability of the Gram bound on `N̄_Q`** (`RealLeviChartIntegrableStatement`). -/
theorem realLeviChartIntegrable : RealLeviChartIntegrableStatement := by
  intro c sz γ hγ1 hγ2
  have hcl : Monotone (RealLeviChart.cls sz) := fun p q hpq =>
    not_lt.mp fun h => absurd hpq (not_le.mpr (RealLeviChart.lt_of_cls_lt sz h))
  let γ' : ℕ → ℝ := fun l => if h : l < ∑ i, sz i then γ ⟨l, h⟩ else 0
  have hγ' : ∀ l : Fin (∑ i, sz i), γ' l = γ l := fun l => by
    simp only [γ', dite_eq_left l.isLt]
  have hfin := gen _ (RealLeviChart.cls sz) hcl γ' (fun l hl => by rw [hγ']; exact hγ1 l hl)
    (fun k l hkl h => by rw [hγ']; exact hγ2 k l hkl h)
  simp only [hγ'] at hfin
  have hpos : ∀ X : RealLeviChart.Coord sz → ℝ,
      0 ≤ ∏ l : Fin (∑ i, sz i), GramFormula.gram (l : ℕ) (RealLeviChart.lower sz X) ^ γ l :=
    fun X => Finset.prod_nonneg fun l _ => Real.rpow_nonneg (gram_lowerC_pos hcl X l).le _
  refine ⟨(continuous_prod_gram hcl γ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hpos)]
  exact hfin

end Langlands.Archimedean
