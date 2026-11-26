import Langlands.Global.RankinSelberg.RealLowerBlockChart
import Langlands.Global.RankinSelberg.RealUnequalOrdinaryFamily
import Langlands.Global.RankinSelberg.RealWhittakerTranslatedMellin
import Mathlib.Analysis.Fourier.Inversion

/-! # Descent of vanishing ordinary integrals along the last row

See the paired Markdown.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalLastRowDescent

/-! ### Fourier uniqueness on `ℝ^(n+1) × ℝ` -/

section Fourier

variable {n : ℕ}

/-- The splitting `ℝ^(n+2) ≃ ℝ^(n+1) × ℝ` into the first `n + 1` coordinates and the last one. -/
def splitLast : EuclideanSpace ℝ (Fin (n + 2)) ≃ᵐ (Fin (n + 1) → ℝ) × ℝ :=
  ((MeasurableEquiv.toLp 2 (Fin (n + 2) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last (n + 1)))).trans
      MeasurableEquiv.prodComm

theorem splitLast_apply (v : EuclideanSpace ℝ (Fin (n + 2))) :
    splitLast v = (fun i => v.ofLp (Fin.castSucc i), v.ofLp (Fin.last (n + 1))) := by
  simp [splitLast, MeasurableEquiv.piFinSuccAbove]
  rfl

theorem measurePreserving_splitLast :
    MeasurePreserving (splitLast (n := n)) volume (volume.prod volume) := by
  have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 2))
  have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 2) => (volume : Measure ℝ))
    (Fin.last (n + 1))
  have h3 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin (n + 1) → ℝ)))).comp (h2.comp h1)
  exact h3

theorem inner_eq_split (v w : EuclideanSpace ℝ (Fin (n + 2))) :
    ⟪v, w⟫ = ∑ i, (splitLast v).1 i * (splitLast w).1 i + (splitLast v).2 * (splitLast w).2 := by
  rw [splitLast_apply, splitLast_apply, PiLp.inner_apply, Fin.sum_univ_castSucc]
  simp [mul_comm]

/-- **Fourier uniqueness at a continuity point.** An integrable function on `ℝ^(n+1) × ℝ` whose
Fourier transform vanishes identically vanishes at every point of continuity; here at `(0, 1)`. -/
theorem eq_zero_of_fourier_eq_zero {Ψ : (Fin (n + 1) → ℝ) × ℝ → ℂ}
    (hΨ : Integrable Ψ (volume.prod volume))
    (hF : ∀ (y : Fin (n + 1) → ℝ) (c : ℝ),
      ∫ p : (Fin (n + 1) → ℝ) × ℝ, (Real.fourierChar (∑ i, p.1 i * y i + p.2 * c) : ℂ) * Ψ p
        ∂(volume.prod volume) = 0)
    (hc : ContinuousAt Ψ (0, 1)) : Ψ (0, 1) = 0 := by
  have hmp := measurePreserving_splitLast (n := n)
  let H : EuclideanSpace ℝ (Fin (n + 2)) → ℂ := Ψ ∘ splitLast
  have hH : Integrable H :=
    (hmp.integrable_comp_emb splitLast.measurableEmbedding).mpr hΨ
  have hFH : 𝓕 H = 0 := by
    funext w
    rw [Real.fourier_eq, Pi.zero_apply]
    have h := hmp.integral_comp splitLast.measurableEmbedding
      (fun p => (Real.fourierChar (-(∑ i, p.1 i * (splitLast w).1 i + p.2 * (splitLast w).2)) :
        ℂ) * Ψ p)
    simp only [H, Function.comp_apply, Circle.smul_def, smul_eq_mul]
    have he : ∀ v : EuclideanSpace ℝ (Fin (n + 2)),
        (Real.fourierChar (-⟪v, w⟫) : ℂ) * Ψ (splitLast v) =
          (Real.fourierChar (-(∑ i, (splitLast v).1 i * (splitLast w).1 i +
            (splitLast v).2 * (splitLast w).2)) : ℂ) * Ψ (splitLast v) := fun v => by
      rw [inner_eq_split]
    simp_rw [he]
    rw [h, ← hF (fun i => -(splitLast w).1 i) (-(splitLast w).2)]
    congr 1
    funext p
    congr 3
    simp only [mul_neg, Finset.sum_neg_distrib]
    ring
  set v₀ : EuclideanSpace ℝ (Fin (n + 2)) := splitLast.symm (0, 1)
  have hv₀ : splitLast v₀ = (0, 1) := splitLast.apply_symm_apply _
  have hcont : ContinuousAt H v₀ := by
    have hs : Continuous (splitLast (n := n)) := by
      have he : (splitLast (n := n) : EuclideanSpace ℝ (Fin (n + 2)) → _) =
          fun v => (fun i => v.ofLp (Fin.castSucc i), v.ofLp (Fin.last (n + 1))) :=
        funext splitLast_apply
      rw [he]
      exact (continuous_pi fun i => (continuous_apply _).comp
        (PiLp.continuous_ofLp 2 (fun _ : Fin (n + 2) => ℝ))).prodMk
        ((continuous_apply _).comp (PiLp.continuous_ofLp 2 (fun _ : Fin (n + 2) => ℝ)))
    exact ContinuousAt.comp (hv₀ ▸ hc) hs.continuousAt
  have hinv := hH.fourierInv_fourier_eq (by rw [hFH]; exact integrable_zero _ _ _) hcont
  rw [hFH] at hinv
  have h0 : 𝓕⁻ (0 : EuclideanSpace ℝ (Fin (n + 2)) → ℂ) v₀ = 0 := by
    rw [Real.fourierInv_eq]
    simp
  rw [h0] at hinv
  have : H v₀ = Ψ (0, 1) := by simp only [H, Function.comp_apply, hv₀]
  rw [← this, ← hinv]

attribute [local instance] RealRankZero.unitsMeasurable RealRankZero.unitsBorel

open RealRankZero (invAbs invAbsVolume unitsHaar measurable_invAbs)

/-- Extension of a function of `(x, u) ∈ ℝ^(n+1) × ℝˣ` by `0` at `u = 0`. -/
def unitsExtend2 (G : (Fin (n + 1) → ℝ) × ℝˣ → ℂ) (p : (Fin (n + 1) → ℝ) × ℝ) : ℂ :=
  if h : p.2 = 0 then 0 else G (p.1, Units.mk0 p.2 h)

theorem unitsExtend2_val (G : (Fin (n + 1) → ℝ) × ℝˣ → ℂ) (p : (Fin (n + 1) → ℝ) × ℝˣ) :
    unitsExtend2 G (p.1, (p.2 : ℝ)) = G p := by
  simp only [unitsExtend2, p.2.ne_zero, dite_false]
  congr
  exact Units.mk0_val _ _

theorem measurableEmbedding_prodVal :
    MeasurableEmbedding (Prod.map (id : (Fin (n + 1) → ℝ) → _) (Units.val : ℝˣ → ℝ)) :=
  MeasurableEmbedding.id.prodMap RealRankZero.measurableEmbedding_val

theorem map_prodVal :
    (volume.prod unitsHaar).map (Prod.map (id : (Fin (n + 1) → ℝ) → _) (Units.val : ℝˣ → ℝ)) =
      ((volume : Measure (Fin (n + 1) → ℝ)).prod (volume : Measure ℝ)).withDensity
        fun q => (invAbs q.2 : ℝ≥0∞) := by
  have : SigmaFinite unitsHaar := inferInstance
  rw [← Measure.map_prod_map _ _ measurable_id RealRankZero.measurableEmbedding_val.measurable,
    Measure.map_id, RealRankZero.map_val_unitsHaar, invAbsVolume,
    prod_withDensity_right (g := fun x : ℝ => (invAbs x : ℝ≥0∞))
      (measurable_coe_nnreal_ennreal.comp measurable_invAbs)]

/-- Integrals against `dx |u|⁻¹ du` on `ℝ^(n+1) × ℝˣ` as Lebesgue integrals. -/
theorem integrable_units_iff (G : (Fin (n + 1) → ℝ) × ℝˣ → ℂ) :
    Integrable G (volume.prod unitsHaar) ↔
      Integrable (fun q => (invAbs q.2 : ℂ) * unitsExtend2 G q) (volume.prod volume) := by
  have h := measurableEmbedding_prodVal (n := n).integrable_map_iff
    (μ := volume.prod unitsHaar) (g := unitsExtend2 G)
  have hc : unitsExtend2 G ∘ Prod.map id Units.val = G := funext fun p => unitsExtend2_val G p
  rw [hc, map_prodVal] at h
  rw [← h, integrable_withDensity_iff_integrable_smul
    (f := fun q : (Fin (n + 1) → ℝ) × ℝ => invAbs q.2) (measurable_invAbs.comp measurable_snd)]
  apply integrable_congr
  filter_upwards [] with q
  rw [NNReal.smul_def, Complex.real_smul]

theorem integral_units_eq (G : (Fin (n + 1) → ℝ) × ℝˣ → ℂ) :
    ∫ p, G p ∂(volume.prod unitsHaar) =
      ∫ q, (invAbs q.2 : ℂ) * unitsExtend2 G q ∂(volume.prod volume) := by
  have h := measurableEmbedding_prodVal (n := n).integral_map
    (μ := volume.prod unitsHaar) (unitsExtend2 G)
  have hc : unitsExtend2 G ∘ Prod.map id Units.val = G := funext fun p => unitsExtend2_val G p
  simp only [← Function.comp_apply (f := unitsExtend2 G), hc] at h
  rw [← h, map_prodVal, integral_withDensity_eq_integral_smul
    (f := fun q : (Fin (n + 1) → ℝ) × ℝ => invAbs q.2) (measurable_invAbs.comp measurable_snd)]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  change invAbs q.2 • unitsExtend2 G q = _
  rw [NNReal.smul_def, Complex.real_smul]

/-- **Fourier uniqueness in last-row coordinates.** If `G` is integrable for `dx |u|⁻¹ du`, all
its Fourier coefficients `∫ e(⟨x, y⟩ + u c) G(x, u)` vanish, and its extension by zero is
continuous at `(0, 1)`, then `G(0, 1) = 0`. -/
theorem eq_zero_of_fourier_units_eq_zero {G : (Fin (n + 1) → ℝ) × ℝˣ → ℂ}
    (hG : Integrable G (volume.prod unitsHaar))
    (hF : ∀ (y : Fin (n + 1) → ℝ) (c : ℝ),
      ∫ p : (Fin (n + 1) → ℝ) × ℝˣ, (Real.fourierChar (∑ i, p.1 i * y i + p.2 * c) : ℂ) * G p
        ∂(volume.prod unitsHaar) = 0)
    (hc : ContinuousAt (unitsExtend2 G) (0, 1)) : G (0, 1) = 0 := by
  let Ψ : (Fin (n + 1) → ℝ) × ℝ → ℂ := fun q => (invAbs q.2 : ℂ) * unitsExtend2 G q
  have hΨ : Integrable Ψ (volume.prod volume) := (integrable_units_iff G).mp hG
  have hΨF : ∀ (y : Fin (n + 1) → ℝ) (c : ℝ),
      ∫ p : (Fin (n + 1) → ℝ) × ℝ, (Real.fourierChar (∑ i, p.1 i * y i + p.2 * c) : ℂ) * Ψ p
        ∂(volume.prod volume) = 0 := by
    intro y c
    have h := integral_units_eq
      (fun p : (Fin (n + 1) → ℝ) × ℝˣ =>
        (Real.fourierChar (∑ i, p.1 i * y i + p.2 * c) : ℂ) * G p)
    rw [hF y c] at h
    rw [h]
    congr 1
    funext q
    simp only [Ψ, unitsExtend2]
    split_ifs with hq
    · simp [hq, invAbs]
    · simp only [Units.val_mk0]
      ring
  have hΨc : ContinuousAt Ψ (0, 1) := by
    have hinv : ContinuousAt (fun q : (Fin (n + 1) → ℝ) × ℝ => (invAbs q.2 : ℂ)) (0, 1) := by
      have h1 : ContinuousAt (fun x : ℝ => ((‖x‖₊⁻¹ : ℝ≥0) : ℂ)) 1 := by
        have : ContinuousAt (fun x : ℝ => (‖x‖⁻¹ : ℝ)) 1 :=
          continuous_norm.continuousAt.inv₀ (by norm_num)
        have h2 : (fun x : ℝ => ((‖x‖₊⁻¹ : ℝ≥0) : ℂ)) = fun x => ((‖x‖⁻¹ : ℝ) : ℂ) := by
          funext x
          simp
        rw [h2]
        exact Complex.continuous_ofReal.continuousAt.comp this
      exact h1.comp_of_eq continuous_snd.continuousAt rfl
    exact hinv.mul hc
  have h0 := eq_zero_of_fourier_eq_zero hΨ hΨF hΨc
  have hval : unitsExtend2 G (0, 1) = G (0, 1) := unitsExtend2_val G (0, 1)
  simp only [Ψ, invAbs, nnnorm_one, inv_one, NNReal.coe_one, Complex.ofReal_one, one_mul] at h0
  rwa [hval] at h0

end Fourier

/-! ### Upper column unipotents and the last-row phase -/

section Column

variable {r m : ℕ}

local notation "G" => fun n => Langlands.GeneralLinear n ℝ

/-- The entries `y_i`, `i < m`, in column `m` of an `(r+1) × (r+1)` matrix. -/
def colEntries (y : Fin m → ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  fun i j => if hi : i.val < m then (if j.val = m then y ⟨i.val, hi⟩ else 0) else 0

theorem colEntries_mul (y y' : Fin m → ℝ) :
    (colEntries y : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) * colEntries y' = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k.val < m
  · have hk' : k.val ≠ m := ne_of_lt hk
    simp [colEntries, hk']
  · simp [colEntries, hk]

/-- The upper column unipotent `1 + Σ_(i<m) y_i E_(i,m)` of `GL_(r+1)(ℝ)`. -/
def colUnip (y : Fin m → ℝ) : Langlands.GeneralLinear (r + 1) ℝ where
  val := 1 + colEntries y
  inv := 1 - colEntries y
  val_inv := by rw [add_mul, one_mul, mul_sub, mul_one, colEntries_mul]; abel
  inv_val := by rw [sub_mul, one_mul, mul_add, mul_one, colEntries_mul]; abel

theorem colUnip_val (y : Fin m → ℝ) :
    ((colUnip y : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) =
      1 + colEntries y := rfl

theorem colEntries_eq_zero_of_le (y : Fin m → ℝ) {i j : Fin (r + 1)} (h : j ≤ i) :
    (colEntries y : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i j = 0 := by
  by_cases hi : i.val < m
  · have hj : j.val ≠ m := by
      rw [Fin.le_def] at h
      omega
    simp [colEntries, hi, hj]
  · simp [colEntries, hi]

theorem colUnip_mem (y : Fin m → ℝ) :
    (colUnip y : Langlands.GeneralLinear (r + 1) ℝ) ∈
      Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ := by
  constructor
  · intro i j hij
    change j < i at hij
    change (1 + colEntries y : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i j = 0
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij),
      colEntries_eq_zero_of_le y hij.le, add_zero]
  · intro i
    change (1 + colEntries y : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i i = 1
    rw [Matrix.add_apply, Matrix.one_apply_eq, colEntries_eq_zero_of_le y le_rfl, add_zero]

/-- The Whittaker character reads the last entry `y_(m-1)` of the column. -/
theorem character_colUnip (a : ℝˣ) (y : Fin (m + 1) → ℝ)
    (hm' : m + 1 < r + 1) :
    realWhittakerCharacter a (colUnip (r := r) y) =
      (Real.fourierChar ((a : ℝ) * y (Fin.last m)) : ℂ) := by
  unfold realWhittakerCharacter
  rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    Langlands.LocalFactor.Archimedean.realScaledCharacter_apply]
  congr 3
  rw [Fintype.sum_eq_single (⟨m, by omega⟩ : Fin r)]
  · have hne : (Fin.castSucc (⟨m, by omega⟩ : Fin r)) ≠ Fin.succ (⟨m, by omega⟩ : Fin r) :=
      ne_of_lt Fin.castSucc_lt_succ
    rw [colUnip_val, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
    simp [colEntries, Fin.last]
  · intro i hi
    have hi' : i.val ≠ m := fun h => hi (Fin.ext h)
    have hne : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
    rw [colUnip_val, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
    by_cases ha : i.val < m + 1
    · simp [colEntries, ha, hi']
    · simp [colEntries, ha]

theorem sum_castLE {N : ℕ} (hm : m ≤ N) (f : Fin N → ℝ) (hf : ∀ k : Fin N, m ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k : Fin m, f (Fin.castLE hm k) := by
  let e : Fin m ↪ Fin N := ⟨Fin.castLE hm, Fin.castLE_injective hm⟩
  have hs : ∑ k ∈ Finset.univ.map e, f k = ∑ k : Fin N, f k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    apply hf
    by_contra hn
    apply hk
    exact Finset.mem_map.mpr ⟨⟨k.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
  rw [← hs, Finset.sum_map]
  rfl

open UnequalAnalytic in
theorem padGL_mul_colEntries (hp : m ≤ r + 1) (g : Langlands.GeneralLinear m ℝ)
    (y : Fin m → ℝ) :
    ((padGL hp g : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) *
        colEntries y = colEntries (Matrix.mulVec g.val y) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hj : j.val = m
  · rw [sum_castLE hp _ (fun k hk => by simp [colEntries, show ¬ k.val < m by omega])]
    by_cases hi : i.val < m
    · simp only [colEntries, hi, hj, dite_true, ite_true, Fin.val_castLE, Fin.is_lt]
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      rw [padGL_apply, dite_eq_left ⟨hi, k.isLt⟩]
      rfl
    · simp only [colEntries, hi, dite_false]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [padGL_apply, dite_eq_right (fun h => hi h.1), Matrix.one_apply_ne]
      · simp
      · intro h
        apply hi
        rw [h]
        exact k.isLt
  · simp [colEntries, hj]

open UnequalAnalytic in
theorem colEntries_mul_padGL (hp : m ≤ r + 1) (g : Langlands.GeneralLinear m ℝ)
    (z : Fin m → ℝ) :
    (colEntries z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) *
        ((padGL hp g : Langlands.GeneralLinear (r + 1) ℝ) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) = colEntries z := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val < m
  · by_cases hmr : m < r + 1
    · let c : Fin (r + 1) := ⟨m, hmr⟩
      rw [Fintype.sum_eq_single c]
      · have hrow : ((padGL hp g : Langlands.GeneralLinear (r + 1) ℝ) :
            Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) c j = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) c j := by
          rw [padGL_apply, dite_eq_right (fun h => lt_irrefl m h.1)]
        rw [hrow]
        by_cases hcj : c = j
        · subst hcj
          simp [colEntries, hi, c]
        · have hj : j.val ≠ m := fun h => hcj (Fin.ext h.symm)
          simp [colEntries, hi, hj, Matrix.one_apply_ne hcj, c]
      · intro k hk
        have hk' : k.val ≠ m := fun h => hk (Fin.ext h)
        simp [colEntries, hi, hk']
    · have hj : j.val ≠ m := by omega
      simp only [colEntries, hi, hj, dite_true, ite_false]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hk : k.val ≠ m := by omega
      simp [hk]
  · simp [colEntries, hi]

/-- `diag(g, 1) (1 + E(y)) = (1 + E(g y)) diag(g, 1)`. -/
theorem padGL_mul_colUnip (hp : m ≤ r + 1) (g : Langlands.GeneralLinear m ℝ) (y : Fin m → ℝ) :
    padGL hp g * colUnip (r := r) y =
      colUnip (r := r) (Matrix.mulVec g.val y) * padGL hp g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, colUnip_val, colUnip_val, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, padGL_mul_colEntries, colEntries_mul_padGL]

end Column

/-! ### The phase of column translates and the integrand at chart points -/

section Integrand

open ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow_unipotent_mul)
open Langlands.QuotientIntegration (descend descend_mk)
open RealUnequalFamily (HasLeftCharacter integrand_mk)
open RealEqualConvergence (logDet)
open RealLowerBlockChart (lastRowChart rowEquiv unitsLower)
open Langlands.GeneralLinear (lowerBlockPair lowerBlockPair_mul_lowerBlockPair
  lowerTriangularSubgroup)

/-- The last row of a representative, as a function on `N_(k+1) \ GL_(k+1)(ℝ)`. -/
def lastRowQ {k : ℕ} : LeftUnipotentQuotient k ℝ → Fin (k + 1) → ℝ :=
  descend _ Langlands.RankinSelberg.lastRow fun u g => lastRow_unipotent_mul u g

@[simp] theorem lastRowQ_mk {k : ℕ} (g : Langlands.GeneralLinear (k + 1) ℝ) :
    lastRowQ (Quotient.mk _ g : LeftUnipotentQuotient k ℝ) = Langlands.RankinSelberg.lastRow g := rfl

theorem hasLeftCharacter_translate {n : ℕ} {a : ℝˣ} {W : Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hW : HasLeftCharacter a W) (c : Langlands.GeneralLinear (n + 1) ℝ) :
    HasLeftCharacter a (fun x => W (x * c)) := by
  intro u hu x
  change W (u * x * c) = _ * W (x * c)
  rw [mul_assoc]
  exact hW u hu (x * c)

variable {r k : ℕ} (h : k < r)

/-- Right translation by an upper column unipotent multiplies the ordinary integrand by the
phase `e(a ⟨ξ, y⟩)` of the last row `ξ`. -/
theorem integrand_colUnip {a : ℝˣ} {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    {V : Langlands.GeneralLinear (k + 1) ℝ → ℂ} (hW : HasLeftCharacter a W)
    (hV : HasLeftCharacter (-a) V) (y : Fin (k + 1) → ℝ) (s : ℂ)
    (q : LeftUnipotentQuotient k ℝ) :
    realUnequalIntegrand h (fun x => W (x * colUnip (r := r) y)) V s q =
      (Real.fourierChar ((a : ℝ) * ∑ j, lastRowQ q j * y j) : ℂ) *
        realUnequalIntegrand h W V s q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [integrand_mk h (hasLeftCharacter_translate hW _) hV, integrand_mk h hW hV, lastRowQ_mk]
    change W (padGL _ g * colUnip y) * _ * _ = _
    rw [padGL_mul_colUnip, hW _ (colUnip_mem _), character_colUnip a _ (by omega)]
    have hrow : Matrix.mulVec g.val y (Fin.last k) = ∑ j, Langlands.RankinSelberg.lastRow g j * y j := rfl
    rw [hrow]
    ring

theorem hasLeftCharacter_pad {n : ℕ} {a : ℝˣ} {V : Langlands.GeneralLinear (n + 1 + 1) ℝ → ℂ}
    (hV : HasLeftCharacter a V) (hp : n + 1 ≤ n + 1 + 1) :
    HasLeftCharacter a (fun z => V (padGL hp z)) := by
  intro u hu z
  change V (padGL hp (u * z)) = _ * V (padGL hp z)
  rw [map_mul, hV _ (RealUnequalConvergence.padGL_mem_upperUnipotent hp hu),
    RealUnequalConvergence.realWhittakerCharacter_padGL (Nat.lt_succ_self n) hp]

section Chart

variable {n : ℕ}

/-- The block matrix `[[1, 0], [x, u]]` of `GL_(n+2)(ℝ)`. -/
def lastRowFactor (x : Fin (n + 1) → ℝ) (u : ℝˣ) : Langlands.GeneralLinear (n + 1 + 1) ℝ :=
  lowerBlockPair (1 : Langlands.GeneralLinear (n + 1) ℝ) (rowEquiv x) (unitsLower u)

theorem lowerBlockPair_zero_one (g : Langlands.GeneralLinear (n + 1) ℝ) :
    lowerBlockPair g (0 : Matrix (Fin 1) (Fin (n + 1)) ℝ) (1 : lowerTriangularSubgroup 1 ℝ) =
      padGL (Nat.le_succ (n + 1)) g := by
  apply Units.ext
  ext i j
  rw [UnequalAnalytic.padGL_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Langlands.GeneralLinear.lowerBlockPair_11, dite_eq_left ⟨i.isLt, j.isLt⟩]
    rfl
  · rw [Langlands.GeneralLinear.lowerBlockPair_12, dite_eq_right (fun h => by simp at h),
      Matrix.one_apply_ne]
    intro he
    have := congrArg Fin.val he
    simp at this
    omega
  · rw [Langlands.GeneralLinear.lowerBlockPair_21, dite_eq_right (fun h => by simp at h),
      Matrix.one_apply_ne]
    · rfl
    · intro he
      have := congrArg Fin.val he
      simp at this
      omega
  · rw [Langlands.GeneralLinear.lowerBlockPair_22, dite_eq_right (fun h => by simp at h)]
    fin_cases i; fin_cases j
    simp

theorem lowerBlockPair_eq (g : Langlands.GeneralLinear (n + 1) ℝ)
    (X : Matrix (Fin 1) (Fin (n + 1)) ℝ) (b : lowerTriangularSubgroup 1 ℝ) :
    lowerBlockPair g X b = padGL (Nat.le_succ (n + 1)) g * lowerBlockPair 1 X b := by
  rw [← lowerBlockPair_zero_one, lowerBlockPair_mul_lowerBlockPair]
  simp

theorem det_lowerBlockPair (g : Langlands.GeneralLinear (n + 1) ℝ)
    (X : Matrix (Fin 1) (Fin (n + 1)) ℝ) (b : lowerTriangularSubgroup 1 ℝ) :
    (lowerBlockPair g X b).val.det = g.val.det * b.val.val.det := by
  change ((Matrix.fromBlocks g.val 0 X b.val.val).submatrix finSumFinEquiv.symm
    finSumFinEquiv.symm).det = _
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]

theorem logDet_lastRowFactor (x : Fin (n + 1) → ℝ) (u : ℝˣ) :
    logDet (lastRowFactor x u) = Real.log |(u : ℝ)| := by
  rw [logDet, lastRowFactor, det_lowerBlockPair]
  simp [realNormalizedAbs, unitsLower, RealLowerBlockChart.unitsGL]

variable {r : ℕ} (h' : n + 1 < r)

theorem integrand_lastRowChart {a : ℝˣ} {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    {V : Langlands.GeneralLinear (n + 1 + 1) ℝ → ℂ} (hW : HasLeftCharacter a W)
    (hV : HasLeftCharacter (-a) V) (s : ℂ) (g : Langlands.GeneralLinear (n + 1) ℝ)
    (x : Fin (n + 1) → ℝ) (u : ℝˣ) :
    realUnequalIntegrand h' W V s (lastRowChart n (Quotient.mk _ g, x, u)) *
        Complex.exp (-(logDet g : ℂ)) =
      Complex.exp ((s - ((r - (n + 1) : ℕ) : ℂ) / 2) * (Real.log |(u : ℝ)| : ℂ)) *
        realUnequalIntegrand (Nat.lt_of_succ_lt h')
          (fun z => W (z * padGL (Nat.le_of_lt (Nat.succ_lt_succ h')) (lastRowFactor x u)))
          (fun z => V (padGL (Nat.le_succ (n + 1)) z * lastRowFactor x u)) (s - 1 / 2)
          (Quotient.mk _ g) := by
  have hn : n < r := Nat.lt_of_succ_lt h'
  have hW' := hasLeftCharacter_translate hW
    (padGL (Nat.le_of_lt (Nat.succ_lt_succ h')) (lastRowFactor x u))
  have hV' := hasLeftCharacter_pad (hasLeftCharacter_translate hV (lastRowFactor x u))
    (Nat.le_succ (n + 1))
  change realUnequalIntegrand h' W V s (Quotient.mk _ (lowerBlockPair g (rowEquiv x)
    (unitsLower u))) * _ = _
  rw [integrand_mk h' hW hV, integrand_mk hn hW' hV', lowerBlockPair_eq]
  change W (padGL _ (padGL _ g * lastRowFactor x u)) * V (padGL _ g * lastRowFactor x u) *
      Complex.exp ((s - ((r - (n + 1) : ℕ) : ℂ) / 2) *
        (logDet (padGL _ g * lastRowFactor x u) : ℂ)) * Complex.exp (-(logDet g : ℂ)) = _
  have hlog : logDet (padGL (Nat.le_succ (n + 1)) g * lastRowFactor x u) =
      logDet g + Real.log |(u : ℝ)| := by
    rw [← logDet_lastRowFactor x u]
    unfold logDet
    rw [Units.val_mul, Matrix.det_mul, UnequalAnalytic.det_padGL, realNormalizedAbs,
      realNormalizedAbs, realNormalizedAbs, abs_mul,
      Real.log_mul (abs_ne_zero.mpr (RealLowerBlockChart.det_ne_zero g))
        (abs_ne_zero.mpr (RealLowerBlockChart.det_ne_zero _))]
  rw [map_mul, UnequalAnalytic.padGL_padGL, hlog]
  have hcast : ((r - n : ℕ) : ℂ) = ((r - (n + 1) : ℕ) : ℂ) + 1 := by
    rw [show r - n = r - (n + 1) + 1 by omega]
    push_cast
    ring
  rw [hcast]
  simp only [Complex.ofReal_add]
  rw [show ∀ A B C : ℂ, A * B * C * Complex.exp (-(logDet g : ℂ)) =
      A * B * (C * Complex.exp (-(logDet g : ℂ))) from fun A B C => by ring,
    ← Complex.exp_add]
  rw [show Complex.exp ((s - (((r - (n + 1) : ℕ) : ℂ)) / 2) *
        ((logDet g : ℂ) + (Real.log |(u : ℝ)| : ℂ)) + -(logDet g : ℂ)) =
      Complex.exp ((s - ((r - (n + 1) : ℕ) : ℂ) / 2) * (Real.log |(u : ℝ)| : ℂ)) *
        Complex.exp ((s - 1 / 2 - ((((r - (n + 1) : ℕ) : ℂ)) + 1) / 2) * (logDet g : ℂ)) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  ring

end Chart

end Integrand

/-! ### Continuity of the smaller integral in the translation parameter -/

section Continuity

open ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open RealUnequalFamily (HasLeftCharacter HasUniformGauge integrand_mk continuous_integrand
  ordinary_halfPlaneDomination)
open RealWhittakerTranslatedMellin (HasGaugeBound compact_rightTranslate_uniformGauge)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

variable {r n : ℕ}

/-- Uniform gauges survive restriction along `GL_(n+1) → GL_(n+2)` after a compact family of
right translations. -/
theorem hasUniformGauge_pad_translate {V : Langlands.GeneralLinear (n + 1 + 1) ℝ → ℂ}
    (hV : HasGaugeBound V) {K : Set (Langlands.GeneralLinear (n + 1 + 1) ℝ)} (hK : IsCompact K)
    {P : Type*} (S : Set P) (L : P → Langlands.GeneralLinear (n + 1 + 1) ℝ)
    (hL : ∀ p ∈ S, L p ∈ K) :
    HasUniformGauge S (fun p z => V (padGL (Nat.le_succ (n + 1)) z * L p)) := by
  obtain ⟨N, hN⟩ := (compact_rightTranslate_uniformGauge hV K hK).pad (Nat.lt_succ_self n)
    (Nat.le_succ (n + 1))
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun p hp y k => (hb (L p) (hL p hp) y k).trans ?_⟩
  gcongr
  have : 0 ≤ (M : ℝ) * max (y (Fin.last n)) 0 := by positivity
  linarith

theorem hasUniformGauge_translate {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : HasGaugeBound W) {K : Set (Langlands.GeneralLinear (r + 1) ℝ)} (hK : IsCompact K)
    {P : Type*} (S : Set P) (L : P → Langlands.GeneralLinear (r + 1) ℝ)
    (hL : ∀ p ∈ S, L p ∈ K) :
    HasUniformGauge S (fun p z => W (z * L p)) := by
  obtain ⟨N, hN⟩ := compact_rightTranslate_uniformGauge hW K hK
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  exact ⟨C, hC, fun p hp y k => hb (L p) (hL p hp) y k⟩

/-- The simple-root gauge bound survives restriction along `GL_(t+1) → GL_(r+1)`. -/
theorem hasGaugeBound_pad {t : ℕ} (h : t < r) (hp : t + 1 ≤ r + 1)
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} (hW : HasGaugeBound W) :
    HasGaugeBound (fun g : Langlands.GeneralLinear (t + 1) ℝ => W (padGL hp g)) := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun g => ?_⟩
  have hdec := congrArg (padGL hp) (RealIwasawa.npart_mul_torus_mul_kpart g).symm
  rw [map_mul, map_mul, RealUnequalConvergence.padGL_torus] at hdec
  have halpha : RealIwasawa.alpha (padGL hp g) =
      RealUnequalConvergence.padVec r (RealIwasawa.alpha g) := by
    rw [hdec]
    exact RealIwasawa.alpha_iwasawa
      ⟨_, RealUnequalConvergence.padGL_mem_upperUnipotent hp (RealIwasawa.npart g).2⟩ _
      (RealUnequalConvergence.padUnitary hp (RealIwasawa.kpart g))
  refine (hb (padGL hp g)).trans ?_
  rw [halpha, RealUnequalConvergence.rootPos_padVec h, RealUnequalConvergence.sum_abs_padVec h]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  have : 0 ≤ (M : ℝ) * max (RealIwasawa.alpha g (Fin.last t)) 0 := by positivity
  linarith [mul_add (-(M : ℝ)) (RealConvergenceAnalysis.rootPos (RealIwasawa.alpha g))
    (max (RealIwasawa.alpha g (Fin.last t)) 0)]

variable (h' : n + 1 < r)

/-- The smaller ordinary integral of the translates `z ↦ W(z · diag(L, 1))` and
`z ↦ V(diag(z, 1) · L)` is continuous in `L` at `1` on a right half-plane. -/
theorem continuousAt_translateIntegral (D : RealQuotientMeasureData n) {a : ℝˣ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {V : Langlands.GeneralLinear (n + 1 + 1) ℝ → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) (hWc : Continuous W)
    (hVc : Continuous V) (hWg : HasGaugeBound W) (hVg : HasGaugeBound V) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ContinuousAt (fun L : Langlands.GeneralLinear (n + 1 + 1) ℝ =>
      realUnequalIntegral (Nat.lt_of_succ_lt h') D
        (fun z => W (z * padGL (Nat.le_of_lt (Nat.succ_lt_succ h')) L))
        (fun z => V (padGL (Nat.le_succ (n + 1)) z * L)) s) 1 := by
  have hn : n < r := Nat.lt_of_succ_lt h'
  set hp : n + 1 + 1 ≤ r + 1 := Nat.le_of_lt (Nat.succ_lt_succ h') with hhp
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : Langlands.GeneralLinear (n + 1 + 1) ℝ)
  let S : Set (Langlands.GeneralLinear (n + 1 + 1) ℝ × ℂ) := K ×ˢ univ
  let Wf : Langlands.GeneralLinear (n + 1 + 1) ℝ × ℂ → Langlands.GeneralLinear (r + 1) ℝ → ℂ :=
    fun p z => W (z * padGL hp p.1)
  let Vf : Langlands.GeneralLinear (n + 1 + 1) ℝ × ℂ → Langlands.GeneralLinear (n + 1) ℝ → ℂ :=
    fun p z => V (padGL (Nat.le_succ (n + 1)) z * p.1)
  have hWl : ∀ p, HasLeftCharacter a (Wf p) := fun p => hasLeftCharacter_translate hW _
  have hVl : ∀ p, HasLeftCharacter (-a) (Vf p) := fun p =>
    hasLeftCharacter_pad (hasLeftCharacter_translate hV p.1) _
  have hWb : HasUniformGauge S Wf :=
    hasUniformGauge_translate hWg (hKc.image (UnequalAnalytic.continuous_padGL hp)) S
      (fun p => padGL hp p.1) (fun p hpS => ⟨p.1, hpS.1, rfl⟩)
  have hVb : HasUniformGauge S Vf :=
    hasUniformGauge_pad_translate hVg hKc S Prod.fst (fun p hpS => hpS.1)
  obtain ⟨σ, hdom⟩ := ordinary_halfPlaneDomination hn D S Wf Vf Prod.snd hWl hVl hWb hVb
  refine ⟨σ, fun s hs => ?_⟩
  obtain ⟨B, hBi, hB⟩ := hdom s.re
  change ContinuousAt (fun L => ∫ q, realUnequalIntegrand hn (Wf (L, s)) (Vf (L, s)) s q
    ∂D.measure) 1
  refine continuousAt_of_dominated ?_ ?_ hBi ?_
  · exact Filter.Eventually.of_forall fun L => (continuous_integrand hn (hWl _) (hVl _)
      (hWc.comp (continuous_id.mul continuous_const))
      (hVc.comp ((UnequalAnalytic.continuous_padGL _).mul continuous_const)) s).aestronglyMeasurable
  · filter_upwards [hK1] with L hL
    exact ae_of_all _ fun q => hB (L, s) ⟨hL, mem_univ _⟩ hs le_rfl q
  · refine ae_of_all _ fun q => ?_
    change ContinuousAt (fun L => W (padGL _ q.out * padGL hp L) *
      V (padGL (Nat.le_succ (n + 1)) q.out * L) *
        ArchimedeanLocal.detPower realNormalizedAbs q.out (s - ((r - n : ℕ) : ℂ) / 2)) 1
    refine (((hWc.comp (continuous_const.mul (UnequalAnalytic.continuous_padGL hp))).mul
      (hVc.comp (continuous_const.mul continuous_id))).mul continuous_const).continuousAt

end Continuity

/-! ### Descent -/

section Descent

open ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.QuotientIntegration (descend leftQuotient_isOpenQuotientMap leftQuotientMap_apply)
open RealUnequalFamily (HasLeftCharacter HasUniformGauge integrand_mk continuous_integrand
  ordinary_halfPlaneDomination)
open ComplexUnequalFamily (HalfPlaneDomination differentiableOn_integral_of_halfPlaneDomination)
open RealWhittakerTranslatedMellin (HasGaugeBound)
open RealLowerBlockChart (lastRowChart lastRowMeasure lastRowChart_integral quotientDensity
  rowEquiv unitsLower)
open RealUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs)
open Langlands.GeneralLinear (lowerBlockPair)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel RealRankZero.unitsMeasurable RealRankZero.unitsBorel

/-- A function holomorphic on a right half-plane and zero on a smaller right half-plane is zero
on the larger one. -/
theorem eq_zero_on_right {f : ℂ → ℂ} {σ τ : ℝ} (hf : DifferentiableOn ℂ f {s | σ < s.re})
    (hzero : ∀ s : ℂ, τ < s.re → f s = 0) : ∀ s : ℂ, σ < s.re → f s = 0 := by
  let z₀ : ℂ := ((max σ τ + 1 : ℝ) : ℂ)
  have hz₀ : max σ τ < z₀.re := by simp [z₀]
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  exact (hf.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt σ).isPreconnected ((le_max_left _ _).trans_lt hz₀)
    ((isOpen_lt continuous_const Complex.continuous_re).eventually_mem
      ((le_max_right _ _).trans_lt hz₀) |>.mono fun s hs => hzero s hs)

variable {r t : ℕ}

theorem hasUniformGauge_const' {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} (hW : HasGaugeBound W)
    {P : Type*} (S : Set P) : HasUniformGauge S (fun _ : P => W) := by
  have h := hasUniformGauge_translate hW (isCompact_singleton (x := 1)) S (fun _ => 1)
    (fun _ _ => rfl)
  simpa only [mul_one] using h

/-- Holomorphy of an ordinary integral whose integrand is dominated, up to a unimodular factor
independent of `s`, by a dominated family. -/
theorem differentiableOn_of_dominated (h : t < r) (D : RealQuotientMeasureData t)
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {V : Langlands.GeneralLinear (t + 1) ℝ → ℂ}
    {σ : ℝ} (hmeas : ∀ s, AEStronglyMeasurable (realUnequalIntegrand h W V s) D.measure)
    (hdom : HalfPlaneDomination D.measure (univ : Set ℂ) id
      (fun s q => realUnequalIntegrand h W V s q) σ) :
    DifferentiableOn ℂ (fun s => realUnequalIntegral h D W V s) {s | σ < s.re} := by
  have hdiff (q : LeftUnipotentQuotient t ℝ) :
      DifferentiableOn ℂ (fun s => realUnequalIntegrand h W V s q) (univ : Set ℂ) := by
    change DifferentiableOn ℂ (fun s => W _ * V _ *
      Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * _)) univ
    exact ((differentiable_const _).mul (Complex.differentiable_exp.comp
      ((differentiable_id.sub_const _).mul_const _))).differentiableOn
  have hd := (differentiableOn_integral_of_halfPlaneDomination isOpen_univ differentiable_id
    hmeas hdiff hdom).2
  rw [univ_inter] at hd
  convert hd using 1 <;> rfl

section ChartFacts

variable {n : ℕ}

theorem continuous_lastRowQ : Continuous (lastRowQ (k := n)) := by
  apply (leftQuotient_isOpenQuotientMap
    (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ)).isQuotientMap.continuous_iff.mpr
  change Continuous fun g : Langlands.GeneralLinear (n + 1) ℝ =>
    fun j => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (Fin.last n) j
  exact continuous_pi fun j => (Units.continuous_val.matrix_elem _ _)

theorem lastRowQ_chart (q : LeftUnipotentQuotient n ℝ) (x : Fin (n + 1) → ℝ) (u : ℝˣ)
    (y : Fin (n + 1 + 1) → ℝ) :
    ∑ j, lastRowQ (lastRowChart n (q, x, u)) j * y j =
      ∑ i, x i * y (Fin.castSucc i) + (u : ℝ) * y (Fin.last (n + 1)) := by
  induction q using Quotient.inductionOn with
  | h g =>
    change ∑ j, Langlands.RankinSelberg.lastRow
      (lowerBlockPair g (rowEquiv x) (unitsLower u)) j * y j = _
    rw [Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      change lowerBlockPair g (rowEquiv x) (unitsLower u) (Fin.natAdd (n + 1) (0 : Fin 1))
        (Fin.castAdd 1 i) * _ = _
      rw [Langlands.GeneralLinear.lowerBlockPair_21]
      rfl
    · change lowerBlockPair g (rowEquiv x) (unitsLower u) (Fin.natAdd (n + 1) (0 : Fin 1))
        (Fin.natAdd (n + 1) (0 : Fin 1)) * _ = _
      rw [Langlands.GeneralLinear.lowerBlockPair_22]
      rfl

theorem continuous_lastRowFactor :
    Continuous (fun p : (Fin (n + 1) → ℝ) × ℝˣ => lastRowFactor p.1 p.2) := by
  have hrow : Continuous (rowEquiv (n := n)) := by
    change Continuous fun x : Fin (n + 1) → ℝ => (fun _ : Fin 1 => x)
    exact continuous_pi fun _ => continuous_id
  exact Langlands.GeneralLinear.continuous_lowerBlockPair.comp
    (continuous_const.prodMk ((hrow.comp continuous_fst).prodMk
      ((RealLowerBlockChart.unitsLowerHomeomorph.continuous).comp continuous_snd)))

theorem lastRowFactor_zero_one : lastRowFactor (n := n) 0 1 = 1 := by
  have h0 : rowEquiv (n := n) 0 = 0 := rfl
  have h1 : unitsLower 1 = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i; fin_cases j
    rfl
  rw [lastRowFactor, h0, h1, lowerBlockPair_zero_one, map_one]

export ArchimedeanRealPairIdentity (sigmaCompactSpace_quotient sigmaFinite_measure)

variable {r : ℕ} (h' : n + 1 < r)

/-- The fibre integral over `N_(n+1) \ GL_(n+1)(ℝ)` of the ordinary integrand at the chart
points `[[g, 0], [x, u]]` is `|u|^(s - (r-n-1)/2)` times the smaller ordinary integral at
`s - 1/2` of the translates by `[[1, 0], [x, u]]`. -/
theorem fibre_eq (D : RealQuotientMeasureData n) {a : ℝˣ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {V : Langlands.GeneralLinear (n + 1 + 1) ℝ → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) (s : ℂ) (x : Fin (n + 1) → ℝ)
    (u : ℝˣ) :
    ∫ q, realUnequalIntegrand h' W V s (lastRowChart n (q, x, u))
        ∂(D.measure.withDensity (quotientDensity n)) =
      Complex.exp ((s - ((r - (n + 1) : ℕ) : ℂ) / 2) * (Real.log |(u : ℝ)| : ℂ)) *
        realUnequalIntegral (Nat.lt_of_succ_lt h') D
          (fun z => W (z * padGL (Nat.le_of_lt (Nat.succ_lt_succ h')) (lastRowFactor x u)))
          (fun z => V (padGL (Nat.le_succ (n + 1)) z * lastRowFactor x u)) (s - 1 / 2) := by
  have hf : Measurable fun q : LeftUnipotentQuotient n ℝ => ((quotientDetAbs q)⁻¹).toNNReal :=
    (continuous_real_toNNReal.comp
      (continuous_quotientDetAbs.inv₀ fun q => (quotientDetAbs_pos q).ne')).measurable
  change ∫ q, _ ∂(D.measure.withDensity fun q => (((quotientDetAbs q)⁻¹).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hf]
  change _ = _ * ∫ q, _ ∂D.measure
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  induction q using Quotient.inductionOn with
  | h g =>
    change (((quotientDetAbs (Quotient.mk _ g : LeftUnipotentQuotient n ℝ))⁻¹).toNNReal : ℝ) •
      realUnequalIntegrand h' W V s (lastRowChart n (Quotient.mk _ g, x, u)) =
        Complex.exp ((s - ((r - (n + 1) : ℕ) : ℂ) / 2) * (Real.log |(u : ℝ)| : ℂ)) *
          realUnequalIntegrand (Nat.lt_of_succ_lt h')
            (fun z => W (z * padGL (Nat.le_of_lt (Nat.succ_lt_succ h')) (lastRowFactor x u)))
            (fun z => V (padGL (Nat.le_succ (n + 1)) z * lastRowFactor x u)) (s - 1 / 2)
            (Quotient.mk _ g)
    rw [← integrand_lastRowChart h' hW hV s g x u, RealLowerBlockChart.quotientDetAbs_mk,
      Real.coe_toNNReal _ (inv_nonneg.mpr (abs_nonneg _)), Complex.real_smul, mul_comm]
    congr 1
    rw [RealEqualConvergence.logDet, realNormalizedAbs, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
      Real.exp_neg, Real.exp_log (abs_pos.mpr (RealLowerBlockChart.det_ne_zero g))]

/-- **Descent along the last row.** Let `n + 1 < r`, `W` on `GL_(r+1)(ℝ)` and `V` on
`GL_(n+2)(ℝ)` be continuous with opposite left characters and simple-root gauge bounds. If for
every column `y` the ordinary integral of the right translate of `W` by the upper column
unipotent `1 + Σ y_i E_(i, n+2)` against `V` vanishes on a right half-plane, then the ordinary
integral of `W` against the restriction `V ∘ diag(·, 1)` vanishes on a right half-plane. -/
theorem lastRow_descent (D : RealQuotientMeasureData n) (D' : RealQuotientMeasureData (n + 1))
    {a : ℝˣ} {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    {V : Langlands.GeneralLinear (n + 1 + 1) ℝ → ℂ} (hW : HasLeftCharacter a W)
    (hV : HasLeftCharacter (-a) V) (hWc : Continuous W) (hVc : Continuous V)
    (hWg : HasGaugeBound W) (hVg : HasGaugeBound V)
    (hvan : ∀ y : Fin (n + 1 + 1) → ℝ, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realUnequalIntegral h' D' (fun x => W (x * colUnip (r := r) y)) V s = 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realUnequalIntegral (Nat.lt_of_succ_lt h') D W
        (fun z => V (padGL (Nat.le_succ (n + 1)) z)) s = 0 := by
  have hn : n < r := Nat.lt_of_succ_lt h'
  have := sigmaFinite_measure D
  obtain ⟨σ₀, hdom₀⟩ := ordinary_halfPlaneDomination h' D' (univ : Set ℂ) (fun _ => W)
    (fun _ => V) id (fun _ => hW) (fun _ => hV) (hasUniformGauge_const' hWg _)
    (hasUniformGauge_const' hVg _)
  obtain ⟨σ₁, hcont⟩ := continuousAt_translateIntegral h' D hW hV hWc hVc hWg hVg
  -- the translates vanish on the common half-plane `σ₀ < re s`
  have hvan₀ : ∀ (y : Fin (n + 1 + 1) → ℝ) (s : ℂ), σ₀ < s.re →
      realUnequalIntegral h' D' (fun x => W (x * colUnip (r := r) y)) V s = 0 := by
    intro y
    obtain ⟨τ, hτ⟩ := hvan y
    have hmeas : ∀ s, AEStronglyMeasurable
        (realUnequalIntegrand h' (fun x => W (x * colUnip (r := r) y)) V s) D'.measure :=
      fun s => (continuous_integrand h' (hasLeftCharacter_translate hW _) hV
        (hWc.comp (continuous_id.mul continuous_const)) hVc s).aestronglyMeasurable
    have hdom : HalfPlaneDomination D'.measure (univ : Set ℂ) id
        (fun s q => realUnequalIntegrand h' (fun x => W (x * colUnip (r := r) y)) V s q) σ₀ := by
      intro τ'
      obtain ⟨B, hBi, hB⟩ := hdom₀ τ'
      refine ⟨B, hBi, fun s hs h1 h2 q => ?_⟩
      show ‖realUnequalIntegrand h' (fun x => W (x * colUnip (r := r) y)) V s q‖ ≤ B q
      rw [integrand_colUnip h' hW hV y s q, norm_mul, Circle.norm_coe, one_mul]
      exact hB s hs h1 h2 q
    exact eq_zero_on_right (differentiableOn_of_dominated h' D' hmeas hdom) hτ
  refine ⟨max (σ₀ - 1 / 2) σ₁, fun s' hs' => ?_⟩
  set s : ℂ := s' + 1 / 2 with hsdef
  have hs₀ : σ₀ < s.re := by
    have : (s : ℂ).re = s'.re + 1 / 2 := by simp [hsdef]
    rw [this]
    linarith [le_max_left (σ₀ - 1 / 2) σ₁]
  have hs₁ : σ₁ < (s - 1 / 2).re := by
    have : s - 1 / 2 = s' := by simp [hsdef]
    rw [this]
    exact (le_max_right _ _).trans_lt hs'
  set Φ := realUnequalIntegrand h' W V s with hΦdef
  have hΦc : Continuous Φ := continuous_integrand h' hW hV hWc hVc s
  have hΦi : Integrable Φ D'.measure := by
    obtain ⟨B, hBi, hB⟩ := hdom₀ s.re
    exact hBi.mono' hΦc.aestronglyMeasurable
      (ae_of_all _ fun q => hB s (mem_univ _) hs₀ le_rfl q)
  obtain ⟨C, hC, hchart⟩ := lastRowChart_integral D D'
  have hΦchart : Integrable (Φ ∘ lastRowChart n) (lastRowMeasure n D) :=
    ((hchart Φ hΦc.measurable).1).mp hΦi
  let A := D.measure.withDensity (quotientDensity n)
  let G : (Fin (n + 1) → ℝ) × ℝˣ → ℂ := fun p => ∫ q, Φ (lastRowChart n (q, p.1, p.2)) ∂A
  have hGi : Integrable G (volume.prod RealRankZero.unitsHaar) :=
    hΦchart.integral_prod_right
  -- Fourier coefficients of `G` vanish
  have hGF : ∀ (y : Fin (n + 1) → ℝ) (c : ℝ),
      ∫ p : (Fin (n + 1) → ℝ) × ℝˣ, (Real.fourierChar (∑ i, p.1 i * y i + p.2 * c) : ℂ) * G p
        ∂(volume.prod RealRankZero.unitsHaar) = 0 := by
    intro y c
    let yy : Fin (n + 1 + 1) → ℝ := Fin.snoc (fun i => y i / (a : ℝ)) (c / (a : ℝ))
    have ha : (a : ℝ) ≠ 0 := a.ne_zero
    let f : LeftUnipotentQuotient (n + 1) ℝ → ℂ := fun q =>
      (Real.fourierChar ((a : ℝ) * ∑ j, lastRowQ q j * yy j) : ℂ) * Φ q
    have hfc : Continuous f := by
      refine (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_const.mul (continuous_finsetSum _ fun j _ =>
          ((continuous_apply j).comp continuous_lastRowQ).mul continuous_const)))).mul hΦc
    have h1 : ∫ q, f q ∂D'.measure = 0 := by
      rw [← hvan₀ yy s hs₀]
      exact integral_congr_ae (ae_of_all _ fun q => (integrand_colUnip h' hW hV yy s q).symm)
    have hfi : Integrable f D'.measure :=
      hΦi.mono hfc.aestronglyMeasurable (ae_of_all _ fun q => by
        simp only [f, norm_mul, Circle.norm_coe, one_mul, le_refl])
    have hfchart : Integrable (f ∘ lastRowChart n) (lastRowMeasure n D) :=
      ((hchart f hfc.measurable).1).mp hfi
    have h2 := (hchart f hfc.measurable).2
    rw [h1] at h2
    have h3 : ∫ z, f (lastRowChart n z) ∂lastRowMeasure n D = 0 := by
      have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
      exact (mul_eq_zero.mp h2.symm).resolve_left hC'
    rw [lastRowMeasure, integral_prod_symm (fun z => f (lastRowChart n z)) hfchart] at h3
    rw [← h3]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    change _ = ∫ q, f (lastRowChart n (q, p.1, p.2)) ∂A
    simp only [f]
    simp_rw [lastRowQ_chart]
    rw [integral_const_mul]
    congr 3
    simp only [yy, Fin.snoc_castSucc, Fin.snoc_last]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    · field_simp
  -- continuity of the extension of `G` at `(0, 1)`
  have hGeq : G = fun p => Complex.exp ((s - ((r - (n + 1) : ℕ) : ℂ) / 2) *
      (Real.log |(p.2 : ℝ)| : ℂ)) *
      realUnequalIntegral hn D
        (fun z => W (z * padGL (Nat.le_of_lt (Nat.succ_lt_succ h')) (lastRowFactor p.1 p.2)))
        (fun z => V (padGL (Nat.le_succ (n + 1)) z * lastRowFactor p.1 p.2)) (s - 1 / 2) :=
    funext fun p => fibre_eq h' D hW hV s p.1 p.2
  have hGc : ContinuousAt G (0, 1) := by
    rw [hGeq]
    refine ContinuousAt.mul ?_ ?_
    · refine (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        ((Units.continuous_val.comp continuous_snd).abs.log fun p => ?_)))).continuousAt
      exact abs_ne_zero.mpr p.2.ne_zero
    · exact (hcont (s - 1 / 2) hs₁).comp_of_eq continuous_lastRowFactor.continuousAt
        lastRowFactor_zero_one
  have hGc' : ContinuousAt (unitsExtend2 G) (0, 1) := by
    have he : Topology.IsOpenEmbedding (Prod.map (id : (Fin (n + 1) → ℝ) → _)
        (Units.val : ℝˣ → ℝ)) := Topology.IsOpenEmbedding.id.prodMap Units.isOpenEmbedding_val
    have hcomp : unitsExtend2 G ∘ Prod.map id Units.val = G :=
      funext fun p => unitsExtend2_val G p
    have hGc2 : ContinuousAt (unitsExtend2 G ∘ Prod.map id Units.val)
        ((0 : Fin (n + 1) → ℝ), (1 : ℝˣ)) := by
      rw [hcomp]
      exact hGc
    have := (he.continuousAt_iff (g := unitsExtend2 G)
      (x := ((0 : Fin (n + 1) → ℝ), (1 : ℝˣ)))).mp hGc2
    simpa using this
  have hG0 := eq_zero_of_fourier_units_eq_zero hGi hGF hGc'
  rw [hGeq] at hG0
  simp only [Units.val_one, abs_one, Real.log_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, lastRowFactor_zero_one, map_one, mul_one] at hG0
  have hss : s - 1 / 2 = s' := by simp [hsdef]
  rw [hss] at hG0
  exact hG0

end ChartFacts

end Descent

end Langlands.Global.RankinSelbergGlobal.RealUnequalLastRowDescent

namespace Langlands.Global.RankinSelbergGlobal

open RealUnequalLastRowDescent ArchimedeanLocal

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

/-- **Descent of vanishing ordinary integrals along the last row.** Let `n + 1 < r`, let `W` on
`GL_(r+1)(ℝ)` and `V` on `GL_(n+2)(ℝ)` be continuous, with the left characters of `a` and `-a`
under the upper unipotent groups and simple-root gauge bounds, and let `D`, `D'` be compatible
quotient measure data for `GL_(n+1)` and `GL_(n+2)`. If for every `y ∈ ℝ^(n+2)` the ordinary
integral of `x ↦ W(x (1 + Σ_i y_i E_(i, n+2)))` against `V` vanishes on a right half-plane, then
the ordinary integral of `W` against `z ↦ V(diag(z, 1))` vanishes on a right half-plane. -/
def RealUnequalLastRowDescentStatement : Prop :=
  ∀ (r n : ℕ) (h' : n + 1 < r) (D : RealQuotientMeasureData n)
    (D' : RealQuotientMeasureData (n + 1)) (a : ℝˣ)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (V : Langlands.GeneralLinear (n + 1 + 1) ℝ → ℂ),
    RealUnequalFamily.HasLeftCharacter a W → RealUnequalFamily.HasLeftCharacter (-a) V →
    Continuous W → Continuous V →
    RealWhittakerTranslatedMellin.HasGaugeBound W → RealWhittakerTranslatedMellin.HasGaugeBound V →
    (∀ y : Fin (n + 1 + 1) → ℝ, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realUnequalIntegral h' D' (fun x => W (x * colUnip (r := r) y)) V s = 0) →
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realUnequalIntegral (Nat.lt_of_succ_lt h') D W
        (fun z => V (padGL (Nat.le_succ (n + 1)) z)) s = 0

theorem realUnequalLastRowDescent : RealUnequalLastRowDescentStatement :=
  fun _ _ h' D D' _ _ _ hW hV hWc hVc hWg hVg hvan =>
    lastRow_descent h' D D' hW hV hWc hVc hWg hVg hvan

end Langlands.Global.RankinSelbergGlobal
