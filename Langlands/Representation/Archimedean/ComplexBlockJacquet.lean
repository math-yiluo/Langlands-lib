import Langlands.Representation.Archimedean.ComplexBlockLimit

/-!
# The partial Jacquet integral along the maximal parabolic subgroup `P_{a,k+1}` of `GL_{a+k+1}(ℂ)`

For `h` in the principal series of phase-power characters `χ` of `GL_{a+k+1}(ℂ)` whose last `k+1`
exponents are tied (and strictly below the earlier ones), `T_P h(g) = ∫_X h(n̄(X) g) dX`
(`ComplexBlockJacquet.blockStep`), and for a continuous `φ` on `GL_{k+1}(ℂ)` the function
`h'(g₁) = ∫_{U(k+1)} φ(κ₂) T_P h(diag(g₁, κ₂)) dκ₂` (`ComplexBlockJacquet.blockPair`) is a
`U(a)`-finite function of the principal series of `GL_a(ℂ)` of the characters
`χ_l(z) (|z|²)^{-(k+1)/2}`, assuming `ComplexBlockChartIntegrableStatement`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix ComplexOrder

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexBlockJacquet

open ComplexBlockParabolic ComplexBlockChart ComplexBlockLimit ComplexPartialJacquet
  ComplexJacquetLimit ComplexGramFormula ComplexPrincipalSeriesExtension ComplexDuality
  Langlands.GeneralLinear

/-! ## Right multiplication of `M_{(k+1)×a}(ℂ)` by an invertible matrix -/

section RowMul

variable {a k : ℕ}

/-- `X ↦ X B` on `M_{(k+1)×a}(ℂ) = Fin (k+1) → Fin a → ℂ`, row by row. -/
def rowMulLinearEquiv {B : Matrix (Fin a) (Fin a) ℂ} (hB : B.det ≠ 0) :
    (Fin (k + 1) → Fin a → ℂ) ≃ₗ[ℂ] (Fin (k + 1) → Fin a → ℂ) :=
  LinearEquiv.piCongrRight fun _ => vecMulLinearEquiv hB

theorem det_rowMulLinearEquiv {B : Matrix (Fin a) (Fin a) ℂ} (hB : B.det ≠ 0) :
    LinearMap.det ((rowMulLinearEquiv (k := k) hB : (Fin (k + 1) → Fin a → ℂ) ≃ₗ[ℂ] _) :
      (Fin (k + 1) → Fin a → ℂ) →ₗ[ℂ] (Fin (k + 1) → Fin a → ℂ)) = B.det ^ (k + 1) := by
  have h : ((rowMulLinearEquiv (k := k) hB : (Fin (k + 1) → Fin a → ℂ) ≃ₗ[ℂ] _) :
      (Fin (k + 1) → Fin a → ℂ) →ₗ[ℂ] (Fin (k + 1) → Fin a → ℂ)) =
      LinearMap.pi (fun i : Fin (k + 1) =>
        ((vecMulLinearEquiv hB : (Fin a → ℂ) ≃ₗ[ℂ] (Fin a → ℂ)) :
          (Fin a → ℂ) →ₗ[ℂ] (Fin a → ℂ)).comp (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro X
    rfl
  rw [h, LinearMap.det_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    det_vecMulLinearEquiv]

/-- `X ↦ X B` as a measurable equivalence. -/
def rowMulEquiv {B : Matrix (Fin a) (Fin a) ℂ} (hB : B.det ≠ 0) :
    (Fin (k + 1) → Fin a → ℂ) ≃ᵐ (Fin (k + 1) → Fin a → ℂ) :=
  (LinearEquiv.toContinuousLinearEquiv
    ((rowMulLinearEquiv (k := k) hB).restrictScalars ℝ)).toHomeomorph.toMeasurableEquiv

theorem rowMulEquiv_apply {B : Matrix (Fin a) (Fin a) ℂ} (hB : B.det ≠ 0)
    (X : Fin (k + 1) → Fin a → ℂ) : rowMulEquiv hB X = fun i => X i ᵥ* B := rfl

/-- Lebesgue measure on `M_{(k+1)×a}(ℂ)` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_rows :
    (volume : Measure (Fin (k + 1) → Fin a → ℂ)).IsAddHaarMeasure := by
  rw [volume_pi]
  exact Measure.pi.isAddHaarMeasure _

/-- Lebesgue measure on `M_{(k+1)×a}(ℂ)` transforms under `X ↦ X B` by `|det B|^{-2(k+1)}`. -/
theorem map_rowMulEquiv {B : Matrix (Fin a) (Fin a) ℂ} (hB : B.det ≠ 0) :
    Measure.map (rowMulEquiv (k := k) hB) volume =
      ENNReal.ofReal (((‖B.det‖ ^ 2) ^ (k + 1))⁻¹) •
        (volume : Measure (Fin (k + 1) → Fin a → ℂ)) := by
  set Lr : (Fin (k + 1) → Fin a → ℂ) ≃ₗ[ℝ] (Fin (k + 1) → Fin a → ℂ) :=
    (rowMulLinearEquiv (k := k) hB).restrictScalars ℝ
  have hdet : LinearMap.det (Lr : (Fin (k + 1) → Fin a → ℂ) →ₗ[ℝ] (Fin (k + 1) → Fin a → ℂ)) =
      Complex.normSq B.det ^ (k + 1) := by
    have := LinearMap.det_restrictScalars (R := ℝ) (S := ℂ) (A := Fin (k + 1) → Fin a → ℂ)
      (f := ((rowMulLinearEquiv (k := k) hB : (Fin (k + 1) → Fin a → ℂ) ≃ₗ[ℂ] _) :
        (Fin (k + 1) → Fin a → ℂ) →ₗ[ℂ] (Fin (k + 1) → Fin a → ℂ)))
    rw [det_rowMulLinearEquiv, map_pow, Algebra.norm_complex_apply] at this
    exact this
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin (k + 1) → Fin a → ℂ)))
    (f := (Lr : (Fin (k + 1) → Fin a → ℂ) →ₗ[ℝ] (Fin (k + 1) → Fin a → ℂ)))
    (by rw [hdet]; exact pow_ne_zero _ (Complex.normSq_pos.mpr hB).ne')
  rw [hdet, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (sq_nonneg _) _))] at this
  exact this

theorem integral_rowMul_eq {B : Matrix (Fin a) (Fin a) ℂ} (hB : B.det ≠ 0)
    (f : (Fin (k + 1) → Fin a → ℂ) → ℂ) :
    ∫ X : Fin (k + 1) → Fin a → ℂ, f (fun i => X i ᵥ* B) =
      ((((‖B.det‖ ^ 2) ^ (k + 1))⁻¹ : ℝ) : ℂ) * ∫ X, f X := by
  have h := integral_map_equiv (μ := (volume : Measure (Fin (k + 1) → Fin a → ℂ)))
    (rowMulEquiv (k := k) hB) f
  rw [map_rowMulEquiv, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (sq_nonneg _) _))] at h
  rw [show (∫ X : Fin (k + 1) → Fin a → ℂ, f (fun i => X i ᵥ* B)) =
      ∫ X, f (rowMulEquiv hB X) from rfl, ← h,
    Complex.real_smul]

end RowMul

/-! ## Block-diagonal and block-lower matrices -/

section Group

variable {a k : ℕ}

theorem blockDiagGL_mul (g₁ g₁' : Langlands.GeneralLinear a ℂ) (g₂ g₂' : Langlands.GeneralLinear k ℂ) :
    blockDiagGL (g₁ * g₁') (g₂ * g₂') = blockDiagGL g₁ g₂ * blockDiagGL g₁' g₂' := by
  apply Units.ext
  rw [Units.val_mul, blockDiagGL_val, blockDiagGL_val, blockDiagGL_val, Units.val_mul,
    Units.val_mul, ComplexBlockParabolic.blockDiag, ComplexBlockParabolic.blockDiag,
    ComplexBlockParabolic.blockDiag, reindex_mul_reindex, Matrix.fromBlocks_multiply]
  simp

theorem blockDiagGL_diagonalUnits (z : Fin a → ℂˣ) :
    blockDiagGL (Iwasawa.diagonalUnits z) (1 : Langlands.GeneralLinear k ℂ) =
      Iwasawa.diagonalUnits (Fin.addCases z (fun _ => 1)) := by
  apply Units.ext
  rw [blockDiagGL_val, Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val, Units.val_one,
    ComplexBlockParabolic.blockDiag]
  ext i j
  refine Fin.addCases (fun p => ?_) (fun q => ?_) i <;>
    refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, Fin.castAdd_inj, Fin.natAdd_inj]
  all_goals
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega

theorem blockDiagGL_mem_upperUnipotent (u : upperUnipotent a ℂ) :
    blockDiagGL (u : Langlands.GeneralLinear a ℂ) (1 : Langlands.GeneralLinear k ℂ) ∈
      upperUnipotent (a + k) ℂ := by
  have hval := blockDiagGL_val (u : Langlands.GeneralLinear a ℂ) (1 : Langlands.GeneralLinear k ℂ)
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    change j < i at hij
    change ((blockDiagGL (u : Langlands.GeneralLinear a ℂ) (1 : Langlands.GeneralLinear k ℂ) :
      Langlands.GeneralLinear (a + k) ℂ) : Matrix (Fin (a + k)) (Fin (a + k)) ℂ) i j = 0
    rw [hval, ComplexBlockParabolic.blockDiag]
    revert hij
    refine Fin.addCases (fun p => ?_) (fun q => ?_) i <;>
      refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j <;> intro hij
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
        Matrix.fromBlocks_apply₁₁]
      exact u.2.1 (by
        rw [Fin.lt_def] at hij ⊢
        simpa using hij)
    · exfalso
      rw [Fin.lt_def] at hij
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hij
      omega
    · simp
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
        Matrix.fromBlocks_apply₂₂, Units.val_one]
      rw [Matrix.one_apply_ne]
      intro h
      subst h
      exact lt_irrefl _ hij
  · change ((blockDiagGL (u : Langlands.GeneralLinear a ℂ) (1 : Langlands.GeneralLinear k ℂ) :
      Langlands.GeneralLinear (a + k) ℂ) : Matrix (Fin (a + k)) (Fin (a + k)) ℂ) i i = 1
    rw [hval, ComplexBlockParabolic.blockDiag]
    refine Fin.addCases (fun p => ?_) (fun q => ?_) i
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
        Matrix.fromBlocks_apply₁₁]
      exact u.2.2 p
    · simp

theorem blockLower_mul_blockDiag_one (X : Matrix (Fin k) (Fin a) ℂ) (B : Matrix (Fin a) (Fin a) ℂ) :
    blockLower X * ComplexBlockParabolic.blockDiag B 1 =
      ComplexBlockParabolic.blockDiag B 1 * blockLower (X * B) := by
  rw [blockLower, blockLower, ComplexBlockParabolic.blockDiag, reindex_mul_reindex,
    reindex_mul_reindex, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem blockLowerGL_mul_blockDiagGL (X : Matrix (Fin k) (Fin a) ℂ)
    (g : Langlands.GeneralLinear a ℂ) :
    blockLowerGL X * blockDiagGL g (1 : Langlands.GeneralLinear k ℂ) =
      blockDiagGL g 1 * blockLowerGL (X * (g : Matrix (Fin a) (Fin a) ℂ)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ComplexBlockChart.blockLowerGL_val,
    ComplexBlockChart.blockLowerGL_val, blockDiagGL_val, Units.val_one]
  exact blockLower_mul_blockDiag_one X _

end Group

/-! ## The shifted characters -/

section Shift

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- The shifted characters `χ_l(z) (|z|²)^{-(k+1)/2}` of `GL_a(ℂ)`. -/
def blockShiftChar (k : ℕ) (χ : ℕ → ℂˣ → ℂ) (l : ℕ) (z : ℂˣ) : ℂ :=
  χ l z * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (-(((k : ℂ) + 1) / 2))

theorem isPhasePower_blockShift (hχ : IsPhasePower χ e) :
    IsPhasePower (blockShiftChar k χ) (fun l => e l - ((k : ℂ) + 1) / 2) where
  eq l z := by
    have hz : ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr z.ne_zero)
    rw [blockShiftChar, blockShiftChar, hχ.eq l z, norm_phaseUnit, one_pow, Complex.ofReal_one,
      Complex.one_cpow, mul_one, mul_assoc, ← Complex.cpow_add _ _ hz]
    congr 2
  one l := by simp [blockShiftChar, hχ.one]
  norm_phase l z := by simp [blockShiftChar, hχ.norm_phase, norm_phaseUnit]

theorem cpow_combine {x : ℂ} (hx : x ≠ 0) (c s₁ s₂ t : ℂ) (n : ℕ) (h : s₁ - n = t + s₂) :
    c * x ^ s₁ * (x ^ n)⁻¹ = c * x ^ t * x ^ s₂ := by
  rw [← Complex.cpow_natCast, ← Complex.cpow_neg, mul_assoc, mul_assoc,
    ← Complex.cpow_add _ _ hx, ← Complex.cpow_add _ _ hx, ← sub_eq_add_neg, h]

theorem principalSeriesCharacter_addCases (hχ1 : ∀ j : ℕ, a ≤ j → χ j 1 = 1)
    (z : Fin a → ℂˣ) :
    principalSeriesCharacter ℂ (a + (k + 1)) χ (Fin.addCases z (fun _ => 1)) *
        ((((∏ i, ‖(z i : ℂ)‖ ^ 2) ^ (k + 1))⁻¹ : ℝ) : ℂ) =
      principalSeriesCharacter ℂ a (blockShiftChar k χ) z := by
  rw [principalSeriesCharacter, principalSeriesCharacter, Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd,
    Units.val_one, norm_one, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]
  rw [Finset.prod_eq_one (fun j _ => hχ1 _ (by omega)), mul_one]
  rw [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_prod, ← Finset.prod_pow,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [blockShiftChar]
  simp only [Complex.finrank_real_complex]
  have hx : ((‖(z i : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr (z i).ne_zero)
  refine cpow_combine hx _ _ _ _ _ ?_
  push_cast
  ring

end Shift

/-! ## The partial Jacquet integral -/

section Step

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- `T_P h(g) = ∫_{M_{(k+1)×a}(ℂ)} h(n̄(X) g) dX`. -/
def blockStep (h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
    (g : Langlands.GeneralLinear (a + (k + 1)) ℂ) : ℂ :=
  ∫ X : Fin (k + 1) → Fin a → ℂ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * g)

theorem of_mul_eq_of_vecMul (X : Fin (k + 1) → Fin a → ℂ) (B : Matrix (Fin a) (Fin a) ℂ) :
    Matrix.of X * B = Matrix.of (fun i => X i ᵥ* B) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

/-- **Equivariance.** `T_P h(diag(b g₁, g₂)) = χ'(b) T_P h(diag(g₁, g₂))` for `b = diag(z) u` in
the Borel subgroup of `GL_a(ℂ)`, with the shifted characters `χ' = blockShiftChar k χ`. -/
theorem blockStep_mul {h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hh : h ∈ principalSeries ℂ (a + (k + 1)) χ) (hχ1 : ∀ j : ℕ, a ≤ j → χ j 1 = 1)
    (z : Fin a → ℂˣ) (u : upperUnipotent a ℂ) (g₁ : Langlands.GeneralLinear a ℂ)
    (g₂ : Langlands.GeneralLinear (k + 1) ℂ) :
    blockStep h (blockDiagGL ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear a ℂ) *
        (u : Langlands.GeneralLinear a ℂ) * g₁) g₂) =
      principalSeriesCharacter ℂ a (blockShiftChar k χ) z * blockStep h (blockDiagGL g₁ g₂) := by
  set b : Langlands.GeneralLinear a ℂ :=
    (Iwasawa.diagonalUnits z : Langlands.GeneralLinear a ℂ) * (u : Langlands.GeneralLinear a ℂ)
    with hbdef
  have hdet : ((b : Langlands.GeneralLinear a ℂ) : Matrix (Fin a) (Fin a) ℂ).det =
      ∏ i, (z i : ℂ) := by
    rw [hbdef, Units.val_mul, Matrix.det_mul, ComplexMaximalParabolicIntegration.det_upperUnipotent u,
      mul_one, Iwasawa.diagonalUnits_val, Matrix.det_diagonal]
  have hdet0 : ((b : Langlands.GeneralLinear a ℂ) : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (z i).ne_zero
  have hsplit : blockDiagGL (b * g₁) g₂ =
      blockDiagGL b (1 : Langlands.GeneralLinear (k + 1) ℂ) * blockDiagGL g₁ g₂ := by
    rw [← blockDiagGL_mul, one_mul]
  have hb : blockDiagGL b (1 : Langlands.GeneralLinear (k + 1) ℂ) =
      (Iwasawa.diagonalUnits (Fin.addCases z (fun _ => 1)) :
        Langlands.GeneralLinear (a + (k + 1)) ℂ) *
      ((⟨blockDiagGL (u : Langlands.GeneralLinear a ℂ) (1 : Langlands.GeneralLinear (k + 1) ℂ),
        blockDiagGL_mem_upperUnipotent u⟩ : upperUnipotent (a + (k + 1)) ℂ) :
          Langlands.GeneralLinear (a + (k + 1)) ℂ) := by
    rw [← blockDiagGL_diagonalUnits]
    change blockDiagGL b 1 = blockDiagGL (Iwasawa.diagonalUnits z) 1 *
      blockDiagGL (u : Langlands.GeneralLinear a ℂ) 1
    rw [← blockDiagGL_mul, one_mul]
  have hpt : ∀ X : Fin (k + 1) → Fin a → ℂ,
      h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL (b * g₁) g₂) =
        principalSeriesCharacter ℂ (a + (k + 1)) χ (Fin.addCases z (fun _ => 1)) *
          h (blockLowerGL (a := a) (k := k + 1)
            (Matrix.of (fun i => X i ᵥ* ((b : Langlands.GeneralLinear a ℂ) :
              Matrix (Fin a) (Fin a) ℂ))) * blockDiagGL g₁ g₂) := by
    intro X
    rw [hsplit, ← mul_assoc, blockLowerGL_mul_blockDiagGL, mul_assoc, of_mul_eq_of_vecMul, hb]
    exact hh.2 _ _ _
  unfold blockStep
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul,
    integral_rowMul_eq hdet0 (fun Y => h (blockLowerGL (a := a) (k := k + 1) (Matrix.of Y) *
      blockDiagGL g₁ g₂)), ← mul_assoc, hdet, norm_prod, ← Finset.prod_pow,
    principalSeriesCharacter_addCases hχ1]

end Step

/-! ## Integrability, continuity and the paired function on `GL_a(ℂ)` -/

section Pair

open scoped Manifold ContDiff Matrix.Norms.Operator

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- The order hypotheses of the block step: `Re e_a = ⋯ = Re e_{a+k}`, `Re e_{l+1} ≤ Re e_l` for
`l < a`, and `Re e_a < Re e_{a−1}`. -/
structure IsBlockDominant (e : ℕ → ℂ) (a k : ℕ) : Prop where
  tie : ∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re
  ord : ∀ l : ℕ, l < a → (e (l + 1)).re ≤ (e l).re
  gap : ∀ l : ℕ, l + 1 = a → (e (l + 1)).re < (e l).re

/-- The tail condition for the exponents `Re e_{l+1} − Re e_l − 1` of the block chart bound. -/
theorem tail_h (he : IsBlockDominant e a k) :
    ∀ j : Fin a, ∑ l : Fin a, (if j ≤ l then
      ((e ((l : ℕ) + 1)).re - (e l).re - 1) + 1 else 0) < 0 := by
  have hord := he.ord
  have hgap := he.gap
  cases a with
  | zero => intro j; exact j.elim0
  | succ m =>
    have h := ComplexPartialSqIntegral.tailCondition_of_le
      (γ := fun l : Fin (m + 1) => (e ((l : ℕ) + 1)).re - (e l).re - 1)
      (fun l => by linarith [hord l l.isLt])
      (by have := hgap m rfl; simp only [Fin.val_last]; linarith)
    intro j
    simpa using h j

theorem integrable_block (hT1 : ComplexBlockChartIntegrableStatement) (hχ : IsPhasePower χ e)
    (he : IsBlockDominant e a k) {h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hh : h ∈ principalSeries ℂ (a + (k + 1)) χ) {κ : Langlands.GeneralLinear (a + (k + 1)) ℂ}
    (hκ : κ ∈ unitaryCompact ℂ (a + (k + 1))) :
    Integrable fun X : Fin (k + 1) → Fin a → ℂ =>
      h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * κ) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hh.1.continuous
  refine Integrable.mono' ((hT1 a (k + 1) _ (tail_h he)).const_mul C) ?_
    (ae_of_all _ fun X => norm_le_block hχ he.tie hh hC (Matrix.of X) hκ)
  exact (hh.1.continuous.comp (continuous_blockLowerGL.mul continuous_const)).aestronglyMeasurable

theorem continuous_blockStep (hT1 : ComplexBlockChartIntegrableStatement) (hχ : IsPhasePower χ e)
    (he : IsBlockDominant e a k) {h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hh : h ∈ principalSeries ℂ (a + (k + 1)) χ) {T : Type*} [TopologicalSpace T]
    [FirstCountableTopology T] {f₁ : T → Langlands.GeneralLinear a ℂ} {f₂ : T → Langlands.GeneralLinear (k + 1) ℂ}
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (hm₁ : ∀ t, f₁ t ∈ unitaryCompact ℂ a)
    (hm₂ : ∀ t, f₂ t ∈ unitaryCompact ℂ (k + 1)) :
    Continuous fun t => blockStep h (blockDiagGL (f₁ t) (f₂ t)) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hh.1.continuous
  refine continuous_of_dominated
    (bound := fun X : Fin (k + 1) → Fin a → ℂ => C * blockChartBound
      (fun l : Fin a => (e ((l : ℕ) + 1)).re - (e l).re - 1) (Matrix.of X))
    (fun t => ?_) (fun t => ae_of_all _ fun X => ?_) ((hT1 a (k + 1) _ (tail_h he)).const_mul C)
    (ae_of_all _ fun X => ?_)
  · exact (hh.1.continuous.comp (continuous_blockLowerGL.mul continuous_const)).aestronglyMeasurable
  · exact norm_le_block hχ he.tie hh hC _ (blockDiagGL_mem_unitaryCompact (hm₁ t) (hm₂ t))
  · exact hh.1.continuous.comp (continuous_const.mul
      (continuous_blockDiagGL.comp (hf₁.prodMk hf₂)))

theorem norm_blockStep_le (hT1 : ComplexBlockChartIntegrableStatement) (hχ : IsPhasePower χ e)
    (he : IsBlockDominant e a k) {h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hh : h ∈ principalSeries ℂ (a + (k + 1)) χ) {C : ℝ}
    (hC : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ‖h κ‖ ≤ C)
    {κ : Langlands.GeneralLinear (a + (k + 1)) ℂ} (hκ : κ ∈ unitaryCompact ℂ (a + (k + 1))) :
    ‖blockStep h κ‖ ≤ ∫ X : Fin (k + 1) → Fin a → ℂ, C * blockChartBound
      (fun l : Fin a => (e ((l : ℕ) + 1)).re - (e l).re - 1) (Matrix.of X) :=
  norm_integral_le_of_norm_le ((hT1 a (k + 1) _ (tail_h he)).const_mul C)
    (ae_of_all _ fun X => norm_le_block hχ he.tie hh hC (Matrix.of X) hκ)

theorem integrable_of_continuous_unitary {n : ℕ} {f : unitaryCompact ℂ n → ℂ}
    (hf : Continuous f) : Integrable f (unitaryHaar n) :=
  integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)

/-- `h'(g₁) = ∫_{U(k+1)} φ(κ₂) T_P h(diag(g₁, κ₂)) dκ₂`. -/
def blockPair (φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ)
    (h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) (g₁ : Langlands.GeneralLinear a ℂ) : ℂ :=
  ∫ κ₂ : unitaryCompact ℂ (k + 1),
    φ κ₂ * blockStep h (blockDiagGL g₁ (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))
    ∂unitaryHaar (k + 1)

theorem blockPair_mul {φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ}
    {h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hh : h ∈ principalSeries ℂ (a + (k + 1)) χ) (hχ1 : ∀ j : ℕ, a ≤ j → χ j 1 = 1)
    (z : Fin a → ℂˣ) (u : upperUnipotent a ℂ) (g₁ : Langlands.GeneralLinear a ℂ) :
    blockPair φ h ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear a ℂ) *
        (u : Langlands.GeneralLinear a ℂ) * g₁) =
      principalSeriesCharacter ℂ a (blockShiftChar k χ) z * blockPair φ h g₁ := by
  unfold blockPair
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun κ₂ => ?_)
  simp only
  rw [blockStep_mul hh hχ1]
  ring

theorem continuous_blockPair (hT1 : ComplexBlockChartIntegrableStatement) (hχ : IsPhasePower χ e)
    (he : IsBlockDominant e a k) {h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hh : h ∈ principalSeries ℂ (a + (k + 1)) χ) {φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ}
    (hφ : Continuous φ) :
    Continuous fun κ : Matrix.unitaryGroup (Fin a) ℂ => blockPair φ h (Unitary.toUnits κ) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hh.1.continuous
  obtain ⟨Cφ, hCφ⟩ := exists_bound_unitaryCompact hφ
  have hCφ0 : 0 ≤ Cφ := le_trans (norm_nonneg _) (hCφ 1 (unitaryCompact ℂ _).one_mem)
  refine continuous_of_dominated (bound := fun _ => Cφ * ∫ X : Fin (k + 1) → Fin a → ℂ,
      C * blockChartBound (fun l : Fin a => (e ((l : ℕ) + 1)).re - (e l).re - 1) (Matrix.of X))
    (fun κ => ?_) (fun κ => ae_of_all _ fun κ₂ => ?_) (integrable_const _)
    (ae_of_all _ fun κ₂ => ?_)
  · exact ((hφ.comp continuous_subtype_val).mul (continuous_blockStep hT1 hχ he hh
      (f₁ := fun _ => Unitary.toUnits κ) continuous_const continuous_subtype_val (fun _ => κ.2)
      (fun t => t.2))).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul (hCφ (κ₂ : Langlands.GeneralLinear (k + 1) ℂ) κ₂.2) (norm_blockStep_le hT1 hχ he hh hC
      (blockDiagGL_mem_unitaryCompact κ.2 κ₂.2)) (norm_nonneg _) hCφ0
  · exact continuous_const.mul (continuous_blockStep hT1 hχ he hh
      (f₁ := fun κ : Matrix.unitaryGroup (Fin a) ℂ => Unitary.toUnits κ)
      (f₂ := fun _ => (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) continuous_unitary_toUnits
      continuous_const (fun κ => κ.2) (fun _ => κ₂.2))

/-- `h ↦ h'` restricted to `U(a)`, as a linear map on a submodule of the principal series. -/
def blockPairOn (hT1 : ComplexBlockChartIntegrableStatement) (hχ : IsPhasePower χ e)
    (he : IsBlockDominant e a k) {φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ} (hφ : Continuous φ)
    (V : Submodule ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ))
    (hV : V ≤ principalSeries ℂ (a + (k + 1)) χ) :
    V →ₗ[ℂ] (Matrix.unitaryGroup (Fin a) ℂ → ℂ) where
  toFun f κ := blockPair φ (f : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) (Unitary.toUnits κ)
  map_add' f g := funext fun κ => by
    have hint : ∀ (f : V) (κ₂ : unitaryCompact ℂ (k + 1)), Integrable fun X : Fin (k + 1) →
        Fin a → ℂ => (f : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
          (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
            blockDiagGL (Unitary.toUnits κ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) :=
      fun f κ₂ => integrable_block hT1 hχ he (hV f.2) (blockDiagGL_mem_unitaryCompact κ.2 κ₂.2)
    have hcont : ∀ f : V, Integrable (fun κ₂ : unitaryCompact ℂ (k + 1) =>
        φ κ₂ * blockStep (f : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
          (blockDiagGL (Unitary.toUnits κ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)))
        (unitaryHaar (k + 1)) := fun f =>
      integrable_of_continuous_unitary ((hφ.comp continuous_subtype_val).mul
        (continuous_blockStep hT1 hχ he (hV f.2) (f₁ := fun _ => Unitary.toUnits κ)
          continuous_const continuous_subtype_val (fun _ => κ.2) (fun t => t.2)))
    simp only [Pi.add_apply]
    rw [blockPair, blockPair, blockPair, ← integral_add (hcont f) (hcont g)]
    refine integral_congr_ae (ae_of_all _ fun κ₂ => ?_)
    simp only [blockStep, Submodule.coe_add, Pi.add_apply]
    rw [integral_add (hint f κ₂) (hint g κ₂), mul_add]
  map_smul' c f := funext fun κ => by
    simp only [blockPair, blockStep, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun κ₂ => ?_)
    simp only
    rw [integral_const_mul]
    ring

theorem blockPair_rightTranslation (φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ)
    (f : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) (g₁ κ : Langlands.GeneralLinear a ℂ) :
    blockPair φ (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
      (blockDiagGL κ (1 : Langlands.GeneralLinear (k + 1) ℂ)) f) g₁ = blockPair φ f (g₁ * κ) := by
  have hpt : ∀ (κ₂ : Langlands.GeneralLinear (k + 1) ℂ) (X : Fin (k + 1) → Fin a → ℂ),
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
        (blockDiagGL κ (1 : Langlands.GeneralLinear (k + 1) ℂ)) f
        (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL g₁ κ₂) =
      f (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL (g₁ * κ) κ₂) := by
    intro κ₂ X
    change f (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL g₁ κ₂ *
      blockDiagGL κ 1) = _
    rw [mul_assoc, ← blockDiagGL_mul, mul_one]
  simp only [blockPair, blockStep, hpt]

theorem finiteDimensional_blockPair (hT1 : ComplexBlockChartIntegrableStatement)
    (hχ : IsPhasePower χ e) (he : IsBlockDominant e a k)
    {h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hh : h ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) χ) (unitaryCompact ℂ (a + (k + 1))))
    {φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ} (hφ : Continuous φ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun κ : Matrix.unitaryGroup (Fin a) ℂ =>
      fun x : Matrix.unitaryGroup (Fin a) ℂ => blockPair φ h (Unitary.toUnits (x * κ)))) := by
  set V := Submodule.span ℂ (Set.range fun κ : unitaryCompact ℂ (a + (k + 1)) =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℂ)
      (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) h) with hVdef
  have hVfin : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hh.2
  have hV : V ≤ principalSeries ℂ (a + (k + 1)) χ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨κ, rfl⟩
    exact rightTranslation_mem_principalSeries (χ := χ) hh.1 _
  have hle : Submodule.span ℂ (Set.range fun κ : Matrix.unitaryGroup (Fin a) ℂ =>
      fun x : Matrix.unitaryGroup (Fin a) ℂ => blockPair φ h (Unitary.toUnits (x * κ))) ≤
      LinearMap.range (blockPairOn hT1 hχ he hφ V hV) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨κ, rfl⟩
    have hκ : blockDiagGL (Unitary.toUnits κ) (1 : Langlands.GeneralLinear (k + 1) ℂ) ∈
        unitaryCompact ℂ (a + (k + 1)) :=
      blockDiagGL_mem_unitaryCompact κ.2 (unitaryCompact ℂ (k + 1)).one_mem
    refine ⟨⟨_, Submodule.subset_span ⟨⟨_, hκ⟩, rfl⟩⟩, funext fun x => ?_⟩
    change blockPair φ _ (Unitary.toUnits x) = blockPair φ h (Unitary.toUnits (x * κ))
    rw [blockPair_rightTranslation, map_mul]
  exact Submodule.finiteDimensional_of_le hle

/-- **The paired function.** `h'` is a `U(a)`-finite function of the principal series of the
shifted characters `blockShiftChar k χ` of `GL_a(ℂ)`. -/
theorem blockPair_mem (hT1 : ComplexBlockChartIntegrableStatement) (hχ : IsPhasePower χ e)
    (he : IsBlockDominant e a k) {h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hh : h ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) χ) (unitaryCompact ℂ (a + (k + 1))))
    {φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ} (hφ : Continuous φ) :
    blockPair φ h ∈ kFiniteFunctions (principalSeries ℂ a (blockShiftChar k χ))
      (unitaryCompact ℂ a) := by
  have hχ1 : ∀ j : ℕ, a ≤ j → χ j 1 = 1 := fun j _ => hχ.one j
  set ψ : Matrix.unitaryGroup (Fin a) ℂ → ℂ := fun κ => blockPair φ h (Unitary.toUnits κ)
    with hψdef
  have hψc : Continuous ψ := continuous_blockPair hT1 hχ he hh.1 hφ
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun κ : Matrix.unitaryGroup (Fin a) ℂ => fun x => ψ (x * κ))) :=
    finiteDimensional_blockPair hT1 hχ he hh hφ
  have hψM : ∀ (d : Fin a → ℂˣ) (κ : Matrix.unitaryGroup (Fin a) ℂ),
      ψ (phaseMatrix d * κ) =
        principalSeriesCharacter ℂ a (blockShiftChar k χ) (fun i => phaseUnit (d i)) * ψ κ := by
    intro d κ
    simp only [hψdef]
    rw [phaseMatrix_toUnits, blockPair_mul hh.1 hχ1]
  have hE := extension_mem_kFiniteFunctions (fun l => e l - ((k : ℂ) + 1) / 2)
    (isPhasePower_blockShift hχ).eq hψc hfin hψM
  convert hE using 1
  funext g
  obtain ⟨z, u, κ, hκ, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  rw [blockPair_mul hh.1 hχ1, hE.1.2 z u κ]
  congr 1
  have hku : κ = Unitary.toUnits (⟨(κ : Matrix (Fin a) (Fin a) ℂ), hκ⟩ :
      Matrix.unitaryGroup (Fin a) ℂ) := Units.ext rfl
  rw [hku, extension_unitary]

end Pair

end ComplexBlockJacquet

open ComplexDuality ComplexBlockParabolic ComplexBlockChart in
/-- **The partial Jacquet integral along `P_{a,k+1}`** (assuming
`ComplexBlockChartIntegrableStatement`). Let `χ_0, χ_1, …` be characters of `ℂˣ` with
`χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1` and `|χ_l| = 1` on the unit circle, such that
`Re e_{l+1} ≤ Re e_l` for `l < a`, `Re e_a < Re e_{a−1}` (if `a ≥ 1`) and
`Re e_a = ⋯ = Re e_{a+k}`. For every `U(a+k+1)`-finite function `h` of the smooth principal series
of `χ` on `GL_{a+k+1}(ℂ)`:
1. `X ↦ h(n̄(X) κ)` is integrable on `M_{(k+1)×a}(ℂ)` for every `κ ∈ U(a+k+1)`, where
   `n̄(X) = [[1, 0], [X, 1]]`;
2. for every continuous `φ` on `GL_{k+1}(ℂ)`, the function
   `g₁ ↦ ∫_{U(k+1)} φ(κ₂) (∫_X h(n̄(X) diag(g₁, κ₂)) dX) dκ₂` (`ComplexBlockJacquet.blockPair`) is a
   `U(a)`-finite function of the smooth principal series of `GL_a(ℂ)` of the characters
   `χ_l(z) (|z|²)^{-(k+1)/2}` (`ComplexBlockJacquet.blockShiftChar k χ`). -/
def ComplexBlockJacquetStatement : Prop :=
  ComplexBlockChartIntegrableStatement →
  ∀ (a k : ℕ) (χ : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ),
    (∀ (l : ℕ) (z : ℂˣ), χ l z =
      χ l (ComplexGramFormula.phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l) →
    (∀ l : ℕ, χ l 1 = 1) →
    (∀ (l : ℕ) (z : ℂˣ), ‖χ l (ComplexGramFormula.phaseUnit z)‖ = 1) →
    (∀ l : ℕ, l < a → (e (l + 1)).re ≤ (e l).re) →
    (∀ l : ℕ, l + 1 = a → (e (l + 1)).re < (e l).re) →
    (∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re) →
    ∀ h ∈ kFiniteFunctions (principalSeries ℂ (a + (k + 1)) χ) (unitaryCompact ℂ (a + (k + 1))),
      (∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), Integrable fun X : Fin (k + 1) → Fin a → ℂ =>
        h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * κ)) ∧
      ∀ φ : Langlands.GeneralLinear (k + 1) ℂ → ℂ, Continuous φ →
        ComplexBlockJacquet.blockPair φ h ∈
          kFiniteFunctions (principalSeries ℂ a (ComplexBlockJacquet.blockShiftChar k χ))
            (unitaryCompact ℂ a)

theorem complexBlockJacquet : ComplexBlockJacquetStatement := by
  intro hT1 a k χ e heq hone hphase hord hgap htie h hh
  have hχ : ComplexPartialJacquet.IsPhasePower χ e := ⟨heq, hone, hphase⟩
  have he : ComplexBlockJacquet.IsBlockDominant e a k := ⟨htie, hord, hgap⟩
  exact ⟨fun κ hκ => ComplexBlockJacquet.integrable_block hT1 hχ he hh.1 hκ,
    fun φ hφ => ComplexBlockJacquet.blockPair_mem hT1 hχ he hh hφ⟩

end Langlands.Archimedean
