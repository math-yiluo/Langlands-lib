import Langlands.Automorphic.CuspidalAdmissible.SiegelGeometry
import Langlands.Global.AdelicOrbitHeightCompactBounds
import Langlands.Global.PrimitiveAdelicBasis
import Langlands.Global.PrimitiveAdelicGauss

/-!
# Heights along torus elements and the key inequality

For the archimedean torus element `A_x = diag(e^{x_i})`, the height of `A_x v` (for a rational
vector `v`) is at least `e^{d x_t}` for every coordinate `t` with `v_t ≠ 0`, and equals
`e^{d x_j}` for the standard basis vector `e_j` (`d = [F : ℚ]`). Combined with a uniform
distortion bound for a compact set `Q`, this gives the key inequality: if
`γ · A_x q = A_{x'} q'` with `q, q' ∈ Q` and the `(t, j)` entry of `γ⁻¹` is nonzero, then
`x'_j ≤ x_t + β` for a constant `β` depending only on `Q`.
-/

noncomputable section

universe u

open scoped NNReal Matrix
open NumberField

set_option autoImplicit false

namespace Langlands.Global.SiegelFiniteness

open PrimitiveAdelicHeight Automorphic.CuspidalL2

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

theorem isPrimitive_rational_single (t : Fin n) :
    IsPrimitive F n (rational F n (Pi.single t 1)) := by
  classical
  refine ⟨1, Pi.single t 1, fun h => (one_ne_zero : (1 : F) ≠ 0) (by simpa using congrFun h t), ?_⟩
  rw [Units.val_one, Matrix.one_mulVec]

/-- The standard basis vectors have height one. -/
theorem height_rational_single (t : Fin n) :
    height F n (rational F n (Pi.single t 1)) = 1 := by
  classical
  have hfin (v : FinitePlace F) : finiteNorm F n (rational F n (Pi.single t 1)) v = 1 := by
    have h : (fun i : Fin n => finiteProjection F v (rational F n (Pi.single t 1) i)) =
        Pi.single t 1 := by
      funext i
      by_cases hi : i = t
      · subst hi
        simp [rational]
      · simp [rational, hi]
    rw [finiteNorm, h, Pi.norm_single, norm_one]
  have hinf (w : InfinitePlace F) : infiniteNorm F n (rational F n (Pi.single t 1)) w = 1 := by
    have h : (fun i : Fin n => infiniteProjection F w (rational F n (Pi.single t 1) i)) =
        Pi.single t 1 := by
      funext i
      by_cases hi : i = t
      · subst hi
        simp [rational]
      · simp [rational, hi]
    rw [infiniteNorm, h, Pi.norm_single, norm_one]
  simp only [height, hfin, hinf, one_pow, Finset.prod_const_one, finprod_one, mul_one]

/-- A single coordinate of a primitive vector has at most its height. -/
theorem height_single_le {y : PrimitiveAdelicHeight.Vector F n} (hy : IsPrimitive F n y) (t : Fin n)
    (hz : IsPrimitive F n (Pi.single t (y t))) :
    height F n (Pi.single t (y t)) ≤ height F n y := by
  classical
  have h := height_le_of_local_le F hz hy zero_le_one (fun v => ?_) (fun w => ?_)
  · simpa using h
  · have e : (fun i : Fin n => finiteProjection F v ((Pi.single t (y t) : PrimitiveAdelicHeight.Vector F n) i)) =
        Pi.single t (finiteProjection F v (y t)) := by
      funext i
      by_cases hi : i = t
      · subst hi
        simp
      · simp [hi]
    rw [finiteNorm, finiteNorm, e, Pi.norm_single]
    exact norm_le_pi_norm (fun i : Fin n => finiteProjection F v (y i)) t
  · have e : (fun i : Fin n => infiniteProjection F w ((Pi.single t (y t) : PrimitiveAdelicHeight.Vector F n) i)) =
        Pi.single t (infiniteProjection F w (y t)) := by
      funext i
      by_cases hi : i = t
      · subst hi
        simp
      · simp [hi]
    rw [infiniteNorm, infiniteNorm, e, Pi.norm_single, one_mul]
    exact norm_le_pi_norm (fun i : Fin n => infiniteProjection F w (y i)) t

theorem realScale_exp_eq (s : ℝ) :
    realScale F (Real.exp s) = (PositiveRealIdeles.full F (expUnit s)).val :=
  rfl

theorem torus_mulVec_apply (x : Fin n → ℝ) (y : PrimitiveAdelicHeight.Vector F n) (i : Fin n) :
    ((AdelicGL.ofInfinite F n (torInf F n x)).val *ᵥ y) i = realScale F (Real.exp (x i)) * y i := by
  rw [ofInfinite_torInf_val, Matrix.mulVec_diagonal]

/-- **Lower bound.** -/
theorem exp_le_height_torus (x : Fin n → ℝ) (v : Fin n → F) (t : Fin n) (ht : v t ≠ 0) :
    Real.exp (x t) ^ Module.finrank ℚ F ≤
      height F n ((AdelicGL.ofInfinite F n (torInf F n x)).val *ᵥ rational F n v) := by
  classical
  have hv : v ≠ 0 := fun h => ht (by rw [h]; rfl)
  have hy : IsPrimitive F n ((AdelicGL.ofInfinite F n (torInf F n x)).val *ᵥ rational F n v) :=
    ⟨_, v, hv, rfl⟩
  set u : Ideles F := PositiveRealIdeles.full F (expUnit (x t)) *
    diagonalUnits F (Units.mk0 (v t) ht) with hudef
  have hyt : ((AdelicGL.ofInfinite F n (torInf F n x)).val *ᵥ rational F n v) t = u.val := by
    rw [torus_mulVec_apply]
    rfl
  have hz : (Pi.single t (((AdelicGL.ofInfinite F n (torInf F n x)).val *ᵥ rational F n v) t) :
      PrimitiveAdelicHeight.Vector F n) = u.val • rational F n (Pi.single t 1) := by
    funext i
    by_cases hi : i = t
    · subst hi
      rw [Pi.single_eq_same, hyt, Pi.smul_apply, smul_eq_mul]
      simp [rational]
    · simp [hi, rational]
  have hzp := (isPrimitive_rational_single F n t).smul F n u
  rw [← hz] at hzp
  have h1 := height_single_le F n hy t hzp
  rw [hz, (isPrimitive_rational_single F n t).height_smul F n, height_rational_single,
    mul_one, hudef, map_mul, IdeleAbsoluteValue.full_diagonalUnits, mul_one,
    absoluteValue_full_expUnit] at h1
  exact h1

/-- **Basis vectors.** -/
theorem height_torus_single (x : Fin n → ℝ) (j : Fin n) :
    height F n ((AdelicGL.ofInfinite F n (torInf F n x)).val *ᵥ rational F n (Pi.single j 1)) =
      Real.exp (x j) ^ Module.finrank ℚ F := by
  classical
  have h : (AdelicGL.ofInfinite F n (torInf F n x)).val *ᵥ rational F n (Pi.single j 1) =
      (PositiveRealIdeles.full F (expUnit (x j))).val • rational F n (Pi.single j 1) := by
    funext i
    rw [torus_mulVec_apply]
    by_cases hi : i = j
    · subst hi
      rfl
    · simp [rational, hi]
  rw [h, (isPrimitive_rational_single F n j).height_smul F n, height_rational_single, mul_one,
    absoluteValue_full_expUnit]

theorem ofInfinite_torInf_inv (x : Fin n → ℝ) :
    (AdelicGL.ofInfinite F n (torInf F n x))⁻¹ = AdelicGL.ofInfinite F n (torInf F n (-x)) := by
  rw [torInf_neg, map_inv]

/-- **The key inequality.** -/
theorem exists_key_bound (hn : 0 < n) {Q : Set (AdelicGL F n)} (hQ : IsCompact Q) :
    ∃ β : ℝ, ∀ (x x' : Fin n → ℝ) (q q' : AdelicGL F n), q ∈ Q → q' ∈ Q →
      ∀ γ : RationalGL F n,
        AdelicGL.rational F n γ * (AdelicGL.ofInfinite F n (torInf F n x) * q) =
          AdelicGL.ofInfinite F n (torInf F n x') * q' →
        ∀ t j : Fin n, (γ⁻¹ : RationalGL F n).val t j ≠ 0 → x' j ≤ x t + β := by
  classical
  obtain ⟨B, hB, hdist⟩ := exists_pos_isHeightDistortionBound_of_isCompact F n hn hQ.inv
  have hd : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.mpr Module.finrank_pos
  refine ⟨2 * Real.log B / Module.finrank ℚ F, fun x x' q q' hq hq' γ hγ t j htj => ?_⟩
  set w : Fin n → F := (γ⁻¹ : RationalGL F n).val *ᵥ Pi.single j 1 with hwdef
  have hwt : w t ≠ 0 := by
    rw [hwdef, Matrix.mulVec_single_one]
    exact htj
  have hw : w ≠ 0 := fun h => hwt (by rw [h]; rfl)
  -- the two vectors agree
  have heq : ((AdelicGL.ofInfinite F n (torInf F n x') * q')⁻¹).val *ᵥ
      rational F n (Pi.single j 1) =
      (q⁻¹).val *ᵥ ((AdelicGL.ofInfinite F n (torInf F n (-x))).val *ᵥ rational F n w) := by
    have e1 : (AdelicGL.rational F n γ * (AdelicGL.ofInfinite F n (torInf F n x) * q))⁻¹ =
        q⁻¹ * AdelicGL.ofInfinite F n (torInf F n (-x)) * AdelicGL.rational F n γ⁻¹ := by
      rw [← ofInfinite_torInf_inv, map_inv]
      group
    rw [← hγ, e1, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← rational_mulVec]
  have hup : height F n (((AdelicGL.ofInfinite F n (torInf F n x') * q')⁻¹).val *ᵥ
      rational F n (Pi.single j 1)) ≤ B * Real.exp (-x' j) ^ Module.finrank ℚ F := by
    rw [mul_inv_rev, ofInfinite_torInf_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
    have h := (hdist q'⁻¹ (Set.inv_mem_inv.mpr hq') _
      ((isPrimitive_rational_single F n j).mulVec F n
        (AdelicGL.ofInfinite F n (torInf F n (-x'))))).1
    rw [height_torus_single] at h
    simpa using h
  have hlo : Real.exp (-x t) ^ Module.finrank ℚ F ≤ B * height F n
      ((q⁻¹).val *ᵥ ((AdelicGL.ofInfinite F n (torInf F n (-x))).val *ᵥ rational F n w)) := by
    have h := (hdist q⁻¹ (Set.inv_mem_inv.mpr hq)
      ((AdelicGL.ofInfinite F n (torInf F n (-x))).val *ᵥ rational F n w)
      ⟨AdelicGL.ofInfinite F n (torInf F n (-x)), w, hw, rfl⟩).2
    refine le_trans ?_ h
    have := exp_le_height_torus F n (-x) w t hwt
    simpa using this
  rw [heq] at hup
  have hcomb : Real.exp (-x t) ^ Module.finrank ℚ F ≤
      B ^ 2 * Real.exp (-x' j) ^ Module.finrank ℚ F := by
    calc Real.exp (-x t) ^ Module.finrank ℚ F ≤ B * (B * Real.exp (-x' j) ^ Module.finrank ℚ F) :=
          hlo.trans (mul_le_mul_of_nonneg_left hup hB.le)
      _ = B ^ 2 * Real.exp (-x' j) ^ Module.finrank ℚ F := by ring
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul] at hcomb
  have hlog := Real.log_le_log (Real.exp_pos _) hcomb
  rw [Real.log_exp, Real.log_mul (pow_pos hB 2).ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_pow] at hlog
  have h2 : (Module.finrank ℚ F : ℝ) * x' j ≤ (Module.finrank ℚ F : ℝ) * x t + 2 * Real.log B := by
    push_cast at hlog
    linarith
  have h3 : x' j - x t ≤ 2 * Real.log B / Module.finrank ℚ F := by
    rw [le_div_iff₀ hd]
    linarith
  linarith

end Langlands.Global.SiegelFiniteness
