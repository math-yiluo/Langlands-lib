import Langlands.Automorphic.CuspidalL2.SiegelCover

/-! # Height bounds for Siegel coordinates with a fixed basis column or row

For an adelic matrix `g` with a rational Siegel decomposition `γ g = torInf(X) q`, `q` in a
fixed compact set, a column of `g` equal to a standard basis vector forces some coordinate
`X k` to be bounded below, and a row of `g` equal to a standard basis vector forces some
coordinate `X k` to be bounded above. Both follow from the product formula and the boundedness
of heights of rows and columns over a compact set of matrices. -/

noncomputable section
universe u
set_option autoImplicit false

open scoped NNReal Matrix
open NumberField Langlands.Global Langlands.Automorphic.CuspidalL2

namespace Langlands.Global.RankinSelbergGlobal.UnequalAnalytic

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The torus element applied to a rational vector, coordinatewise. -/
theorem torus_mulVec_rational_apply (X : Fin n → ℝ) (v : Fin n → F) :
    ((AdelicGL.ofInfinite F n (torInf F n X) : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ PrimitiveAdelicHeight.rational F n v =
      fun i => realScale F (Real.exp (X i)) * diagonal F (v i) := by
  rw [ofInfinite_torInf_val]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

/-- **Product formula lower bound.** If the `k`-th coordinate of the rational vector `v` is
nonzero, the height of `torInf(X) v` is at least `exp([F:ℚ] X k)`. -/
theorem exp_le_height_torus_rational (X : Fin n → ℝ) (v : Fin n → F) (k : Fin n)
    (hk : v k ≠ 0) :
    Real.exp (Module.finrank ℚ F * X k) ≤
      PrimitiveAdelicHeight.height F n
        (((AdelicGL.ofInfinite F n (torInf F n X) : AdelicGL F n) :
          Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ PrimitiveAdelicHeight.rational F n v) := by
  set x := (((AdelicGL.ofInfinite F n (torInf F n X) : AdelicGL F n) :
          Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ PrimitiveAdelicHeight.rational F n v) with hx
  have hv : v ≠ 0 := fun h => hk (by rw [h]; rfl)
  have hprim : PrimitiveAdelicHeight.IsPrimitive F n x :=
    ⟨AdelicGL.ofInfinite F n (torInf F n X), v, hv, rfl⟩
  have hxk : x k = realScale F (Real.exp (X k)) * diagonal F (v k) := by
    rw [hx, torus_mulVec_rational_apply]
  let a : Fˣ := Units.mk0 (v k) hk
  let t : Ideles F := diagonalUnits F a
  have hfull : ((∏ w : InfinitePlace F, ‖t.val.1 w‖ ^ w.mult) *
      ∏ᶠ p : FinitePlace F, ‖t.val.2 p‖) = 1 := by
    rw [← IdeleAbsoluteValue.coe_full, IdeleAbsoluteValue.full_diagonalUnits]
    rfl
  have ht : (fun p : FinitePlace F => ‖t.val.2 p‖).HasFiniteMulSupport :=
    NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm (ideleProductEquiv F t).2
  have hinf : ∀ w : InfinitePlace F,
      Real.exp (X k) * ‖t.val.1 w‖ ≤ PrimitiveAdelicHeight.infiniteNorm F n x w := by
    intro w
    refine le_trans (le_of_eq ?_)
      (norm_le_pi_norm (fun i : Fin n => infiniteProjection F w (x i)) k)
    rw [hxk, map_mul, norm_mul]
    congr 1
    change _ = ‖PositiveRealIdeles.realEmbedding F w (Real.exp (X k))‖
    rw [PositiveRealIdeles.norm_realEmbedding, abs_of_pos (Real.exp_pos _)]
  have hfin : ∀ p : FinitePlace F,
      ‖t.val.2 p‖ ≤ PrimitiveAdelicHeight.finiteNorm F n x p := by
    intro p
    refine le_trans (le_of_eq ?_)
      (norm_le_pi_norm (fun i : Fin n => finiteProjection F p (x i)) k)
    rw [hxk, map_mul]
    change ‖t.val.2 p‖ = ‖(1 : FiniteCompletion F p) * _‖
    rw [one_mul]
    rfl
  have hprodinf : Real.exp (Module.finrank ℚ F * X k) *
      ∏ w : InfinitePlace F, ‖t.val.1 w‖ ^ w.mult ≤
        ∏ w : InfinitePlace F, PrimitiveAdelicHeight.infiniteNorm F n x w ^ w.mult := by
    calc Real.exp (Module.finrank ℚ F * X k) * ∏ w : InfinitePlace F, ‖t.val.1 w‖ ^ w.mult
        = ∏ w : InfinitePlace F, (Real.exp (X k) * ‖t.val.1 w‖) ^ w.mult := by
          simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
            InfinitePlace.sum_mult_eq]
          rw [← Real.exp_nat_mul]
      _ ≤ _ := Finset.prod_le_prod₀ (fun w _ => pow_nonneg (by positivity) _)
          (fun w _ => pow_le_pow_left₀ (by positivity) (hinf w) _)
  have hprodfin : ∏ᶠ p : FinitePlace F, ‖t.val.2 p‖ ≤
      ∏ᶠ p : FinitePlace F, PrimitiveAdelicHeight.finiteNorm F n x p :=
    finprod_le_finprod₀ ht (fun _ => norm_nonneg _) (hprim.hasFiniteMulSupport F n) hfin
  have hfin0 : 0 ≤ ∏ᶠ p : FinitePlace F, ‖t.val.2 p‖ :=
    finprod_nonneg fun _ => norm_nonneg _
  calc Real.exp (Module.finrank ℚ F * X k)
      = Real.exp (Module.finrank ℚ F * X k) *
          ((∏ w : InfinitePlace F, ‖t.val.1 w‖ ^ w.mult) *
            ∏ᶠ p : FinitePlace F, ‖t.val.2 p‖) := by rw [hfull, mul_one]
    _ = (Real.exp (Module.finrank ℚ F * X k) *
          ∏ w : InfinitePlace F, ‖t.val.1 w‖ ^ w.mult) *
            ∏ᶠ p : FinitePlace F, ‖t.val.2 p‖ := (mul_assoc _ _ _).symm
    _ ≤ (∏ w : InfinitePlace F, PrimitiveAdelicHeight.infiniteNorm F n x w ^ w.mult) *
          ∏ᶠ p : FinitePlace F, PrimitiveAdelicHeight.finiteNorm F n x p :=
        mul_le_mul hprodinf hprodfin hfin0
          (Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _)
    _ = PrimitiveAdelicHeight.height F n x := rfl

variable {n}

omit [NumberField F] in
/-- A finite product bounded factorwise by factors at least one. -/
private theorem finprod_le_of_le_of_one_le {f g : FinitePlace F → ℝ} (hf0 : ∀ p, 0 ≤ f p)
    (hg : g.HasFiniteMulSupport) (hg1 : ∀ p, 1 ≤ g p) (hfg : ∀ p, f p ≤ g p) :
    ∏ᶠ p, f p ≤ ∏ᶠ p, g p := by
  by_cases hf : f.HasFiniteMulSupport
  · exact finprod_le_finprod₀ hf hf0 hg hfg
  · rw [finprod_of_infinite_mulSupport hf]
    exact one_le_finprod hg1

/-- Every vector whose local maximum norms are bounded by those of a matrix and its inverse
has height at most the matrix height. -/
theorem height_le_matrixHeight_of_local (hn : 0 < n) (g : AdelicGL F n) (x : Fin n → Adeles F)
    (hinf : ∀ w : InfinitePlace F, PrimitiveAdelicHeight.infiniteNorm F n x w ≤
      AdelicMatrixHeight.infiniteLocal F n g w)
    (hfin : ∀ p : FinitePlace F, PrimitiveAdelicHeight.finiteNorm F n x p ≤
      AdelicMatrixHeight.finiteLocal F n g p) :
    PrimitiveAdelicHeight.height F n x ≤ AdelicMatrixHeight.height F n g := by
  have h1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hprodinf : ∏ w : InfinitePlace F, PrimitiveAdelicHeight.infiniteNorm F n x w ^ w.mult ≤
      ∏ w : InfinitePlace F, ((n : ℝ) * AdelicMatrixHeight.infiniteLocal F n g w) ^ w.mult :=
    Finset.prod_le_prod₀ (fun w _ => pow_nonneg (norm_nonneg _) _)
      (fun w _ => pow_le_pow_left₀ (norm_nonneg _)
        ((hinf w).trans (le_mul_of_one_le_left
          (MatrixInverseHeight.localMaximum_nonneg _ _) h1)) _)
  have hprodfin : ∏ᶠ p : FinitePlace F, PrimitiveAdelicHeight.finiteNorm F n x p ≤
      ∏ᶠ p : FinitePlace F, AdelicMatrixHeight.finiteLocal F n g p :=
    finprod_le_of_le_of_one_le F (fun _ => norm_nonneg _)
      (AdelicMatrixHeight.hasFiniteMulSupport_finiteLocal F n hn g)
      (AdelicMatrixHeight.one_le_finiteLocal F n hn g) hfin
  exact mul_le_mul hprodinf hprodfin (finprod_nonneg fun _ => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => pow_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (MatrixInverseHeight.localMaximum_nonneg _ _)) _)

/-- A column of an adelic matrix has height at most the matrix height. -/
theorem height_column_le (hn : 0 < n) (g : AdelicGL F n) (j : Fin n) :
    PrimitiveAdelicHeight.height F n (fun i => (g : Matrix (Fin n) (Fin n) (Adeles F)) i j) ≤
      AdelicMatrixHeight.height F n g := by
  apply height_le_matrixHeight_of_local F hn g
  · intro w
    refine (pi_norm_le_iff_of_nonneg (MatrixInverseHeight.localMaximum_nonneg _ _)).mpr
      fun i => ?_
    exact MatrixInverseHeight.entry_le_localMaximum (infiniteProjection F w) g i j
  · intro p
    refine (pi_norm_le_iff_of_nonneg (MatrixInverseHeight.localMaximum_nonneg _ _)).mpr
      fun i => ?_
    exact MatrixInverseHeight.entry_le_localMaximum (finiteProjection F p) g i j

/-- A row of an adelic matrix has height at most the matrix height. -/
theorem height_row_le (hn : 0 < n) (g : AdelicGL F n) (i : Fin n) :
    PrimitiveAdelicHeight.height F n (fun j => (g : Matrix (Fin n) (Fin n) (Adeles F)) i j) ≤
      AdelicMatrixHeight.height F n g := by
  apply height_le_matrixHeight_of_local F hn g
  · intro w
    refine (pi_norm_le_iff_of_nonneg (MatrixInverseHeight.localMaximum_nonneg _ _)).mpr
      fun j => ?_
    exact MatrixInverseHeight.entry_le_localMaximum (infiniteProjection F w) g i j
  · intro p
    refine (pi_norm_le_iff_of_nonneg (MatrixInverseHeight.localMaximum_nonneg _ _)).mpr
      fun j => ?_
    exact MatrixInverseHeight.entry_le_localMaximum (finiteProjection F p) g i j

/-- Matrix heights are bounded on a compact set. -/
theorem exists_matrixHeight_le_of_isCompact (hn : 0 < n) {Q : Set (AdelicGL F n)}
    (hQ : IsCompact Q) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ q ∈ Q, AdelicMatrixHeight.height F n q ≤ B := by
  obtain ⟨A, hA⟩ := hQ.bddAbove_image (AdelicMatrixHeight.continuous_height F hn).continuousOn
  exact ⟨max A 1, le_max_right _ _, fun q hq => (hA ⟨q, hq, rfl⟩).trans (le_max_left _ _)⟩

/-- `realScale` of a positive real is invertible with inverse the reciprocal scale. -/
theorem realScale_exp_neg_mul (s : ℝ) (a : Adeles F) :
    realScale F (Real.exp (-s)) * (realScale F (Real.exp s) * a) = a := by
  rw [← mul_assoc, ← realScale_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h1 : realScale F 1 = 1 := Prod.ext (map_one _) rfl
  rw [h1, one_mul]

/-- **Coordinate bounds from a fixed basis column or row.** For a compact set `Q` there is
`C` such that, whenever `γ g = torInf(X) q` with `γ` rational and `q ∈ Q`: if some column of `g`
is a standard basis column then some `X k ≥ -C`, and if some row of `g` is a standard basis
row then some `X k ≤ C`. -/
theorem exists_coordinate_bounds (hn : 0 < n) {Q : Set (AdelicGL F n)} (hQ : IsCompact Q) :
    ∃ C : ℝ, ∀ (g : AdelicGL F n) (γ : RationalGL F n) (X : Fin n → ℝ) (q : AdelicGL F n),
      q ∈ Q → AdelicGL.rational F n γ * g = AdelicGL.ofInfinite F n (torInf F n X) * q →
      ((∃ j, ∀ i, (g : Matrix (Fin n) (Fin n) (Adeles F)) i j =
          (1 : Matrix (Fin n) (Fin n) (Adeles F)) i j) → ∃ k, -C ≤ X k) ∧
      ((∃ i, ∀ j, (g : Matrix (Fin n) (Fin n) (Adeles F)) i j =
          (1 : Matrix (Fin n) (Fin n) (Adeles F)) i j) → ∃ k, X k ≤ C) := by
  obtain ⟨B, hB1, hB⟩ := exists_matrixHeight_le_of_isCompact F hn hQ
  have hd : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.mpr Module.finrank_pos
  refine ⟨Real.log B / Module.finrank ℚ F, fun g γ X q hq hγ => ⟨?_, ?_⟩⟩
  · rintro ⟨j, hj⟩
    -- column `j` of `q` is `torInf(-X)` applied to column `j` of `γ`
    have hcol : (fun i => (q : Matrix (Fin n) (Fin n) (Adeles F)) i j) =
        ((AdelicGL.ofInfinite F n (torInf F n (-X)) : AdelicGL F n) :
          Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ
            PrimitiveAdelicHeight.rational F n (fun i => (γ : Matrix (Fin n) (Fin n) F) i j) := by
      rw [torus_mulVec_rational_apply]
      funext i
      have h := congrArg (fun M : AdelicGL F n => (M : Matrix (Fin n) (Fin n) (Adeles F)) i j) hγ
      simp only [Units.val_mul, Matrix.mul_apply, hj, ofInfinite_torInf_val] at h
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Matrix.diagonal_apply, ite_mul, zero_mul,
        Finset.sum_ite_eq] at h
      have h' : diagonal F ((γ : Matrix (Fin n) (Fin n) F) i j) =
          realScale F (Real.exp (X i)) * (q : Matrix (Fin n) (Fin n) (Adeles F)) i j := h
      rw [Pi.neg_apply, h', realScale_exp_neg_mul]
    obtain ⟨k, hk⟩ : ∃ k, (γ : Matrix (Fin n) (Fin n) F) k j ≠ 0 := by
      by_contra! h0
      have hdet := Matrix.det_eq_zero_of_column_eq_zero j h0
      exact (Matrix.GeneralLinearGroup.det_ne_zero γ) hdet
    refine ⟨k, ?_⟩
    have hlow := exp_le_height_torus_rational F n (-X)
      (fun i => (γ : Matrix (Fin n) (Fin n) F) i j) k hk
    rw [← hcol] at hlow
    have hup := (hlow.trans (height_column_le F hn q j)).trans (hB q hq)
    have hlog := Real.log_le_log (Real.exp_pos _) hup
    rw [Real.log_exp, Pi.neg_apply] at hlog
    rw [neg_le, le_div_iff₀' hd]
    exact hlog
  · rintro ⟨i, hi⟩
    -- row `i` of `q⁻¹` is `torInf(X)` applied to row `i` of `γ⁻¹`
    have hγ' : g * q⁻¹ = AdelicGL.rational F n γ⁻¹ * AdelicGL.ofInfinite F n (torInf F n X) := by
      rw [map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, hγ, mul_assoc, mul_inv_cancel, mul_one]
    have hrow : (fun l => ((q⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) i l) =
        ((AdelicGL.ofInfinite F n (torInf F n X) : AdelicGL F n) :
          Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ
            PrimitiveAdelicHeight.rational F n
              (fun l => ((γ⁻¹ : RationalGL F n) : Matrix (Fin n) (Fin n) F) i l) := by
      rw [torus_mulVec_rational_apply]
      funext l
      have h := congrArg (fun M : AdelicGL F n => (M : Matrix (Fin n) (Fin n) (Adeles F)) i l)
        hγ'
      simp only [Units.val_mul, Matrix.mul_apply, hi, ofInfinite_torInf_val] at h
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, Matrix.diagonal_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq'] at h
      rw [h, mul_comm]
      rfl
    obtain ⟨k, hk⟩ : ∃ k, ((γ⁻¹ : RationalGL F n) : Matrix (Fin n) (Fin n) F) i k ≠ 0 := by
      by_contra! h0
      have hdet := Matrix.det_eq_zero_of_row_eq_zero i h0
      exact (Matrix.GeneralLinearGroup.det_ne_zero γ⁻¹) hdet
    refine ⟨k, ?_⟩
    have hlow := exp_le_height_torus_rational F n X
      (fun l => ((γ⁻¹ : RationalGL F n) : Matrix (Fin n) (Fin n) F) i l) k hk
    rw [← hrow] at hlow
    have hup := (hlow.trans (height_row_le F hn q⁻¹ i)).trans
      ((AdelicMatrixHeight.height_inv F n q).le.trans (hB q hq))
    have hlog := Real.log_le_log (Real.exp_pos _) hup
    rw [Real.log_exp] at hlog
    rw [le_div_iff₀ hd]
    linarith

end Langlands.Global.RankinSelbergGlobal.UnequalAnalytic
