import Langlands.Representation.Archimedean.ComplexBlockChartIntegralProof
import Langlands.Representation.Archimedean.ComplexBlockJacquet

/-!
# Growth bounds for modulus-covariant functions on `GL_n(ℂ)`

Tools for the proof of `ComplexBlockParabolicIntegrationStatement`. A function `F` on `GL_N(ℂ)` is
*norm-covariant* (`NormCov N F`) if `‖F(diag(z) u g)‖ = ∏_l |z_l|^{2(N−1−2l)} ‖F(g)‖` for upper
unipotent `u`; every function of the principal series of the modulus character is, and so are
integrals of `‖F‖` along the opposite unipotent radicals. For such `F` bounded by `C` on `U(N)`:

* `norm_le_blockBound`: `‖F(n̄(X) κ)‖ ≤ C · blockBound a r X` for `X ∈ M_{r×a}(ℂ)`, with
  `blockBound` integrable (`integrable_blockBound`, from `complexBlockChartIntegrable`);
* `norm_le_chartBound`: `‖F(J(x,1) κ)‖ ≤ C ∏_l (1 + |x_l|²)^{−2}`.

It also contains the change of variables `X ↦ h X` on `M_{r×a}(ℂ)` and the block-matrix identities
used in the proof.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Matrix

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexBlockParabolicProof

open ComplexMaximalParabolicIntegration ComplexParabolicChartBound ComplexBlockParabolic
  ComplexBlockChart ComplexKIntegralInvariance Langlands.GeneralLinear ComplexPartialJacquet
  ComplexJacquetLimit

/-! ## Norm-covariant functions -/

section Cov

/-- The exponent `σ_N(l) = 2(N − 1 − 2l)` of `‖δ_B(diag z)‖ = ∏_l |z_l|^{σ_N(l)}`. -/
def modExp (N : ℕ) (l : ℕ) : ℝ := 2 * (((N : ℝ) - 1) - 2 * (l : ℝ))

theorem modExp_sub (N l : ℕ) : (modExp N (l + 1) - modExp N l) / 2 = -2 := by
  unfold modExp
  push_cast
  ring

/-- `‖F(diag(z) u g)‖ = ∏_l |z_l|^{σ_N(l)} ‖F(g)‖` for upper unipotent `u`. -/
def NormCov (N : ℕ) (F : Langlands.GeneralLinear N ℂ → ℂ) : Prop :=
  ∀ (z : Fin N → ℂˣ) (u : upperUnipotent N ℂ) (g : Langlands.GeneralLinear N ℂ),
    ‖F ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear N ℂ) *
      (u : Langlands.GeneralLinear N ℂ) * g)‖ = (∏ l : Fin N, ‖(z l : ℂ)‖ ^ modExp N l) * ‖F g‖

theorem norm_modulus (N : ℕ) (z : Fin N → ℂˣ) :
    ‖principalSeriesCharacter ℂ N (modulusCharacter N) z‖ =
      ∏ l : Fin N, ‖(z l : ℂ)‖ ^ modExp N l := by
  rw [norm_principalSeriesCharacter (isPhasePower_modulus N)]
  refine Finset.prod_congr rfl fun l _ => ?_
  congr 1
  simp only [modExp, Complex.sub_re, Complex.div_re, Complex.natCast_re, Complex.one_re,
    Complex.natCast_im, Complex.sub_im, Complex.one_im]
  norm_num
  ring

theorem normCov_of_mem {N : ℕ} {F : Langlands.GeneralLinear N ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ N (modulusCharacter N)) : NormCov N F := by
  intro z u g
  rw [hF.2 z u g, norm_mul, norm_modulus]

/-- The norm of a norm-covariant function, as a covariant function in the sense of
`ComplexBlockChart.norm_le_gram`. -/
theorem normCov_cast {N : ℕ} {F : Langlands.GeneralLinear N ℂ → ℂ} (hF : NormCov N F)
    (z : Fin N → ℂˣ) (u : upperUnipotent N ℂ) (g : Langlands.GeneralLinear N ℂ) :
    ((‖F ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear N ℂ) *
      (u : Langlands.GeneralLinear N ℂ) * g)‖ : ℝ) : ℂ) =
      ((∏ l : Fin N, ‖(z l : ℂ)‖ ^ modExp N l : ℝ) : ℂ) * ((‖F g‖ : ℝ) : ℂ) := by
  rw [hF z u g, Complex.ofReal_mul]

theorem norm_cast_prod {N : ℕ} (z : Fin N → ℂˣ) :
    ‖((∏ l : Fin N, ‖(z l : ℂ)‖ ^ modExp N l : ℝ) : ℂ)‖ =
      ∏ l : Fin N, ‖(z l : ℂ)‖ ^ modExp N l := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun l _ =>
    Real.rpow_nonneg (norm_nonneg _) _)]

end Cov

/-! ## The block bound -/

section Block

variable {a : ℕ}

/-- The dominating function on `M_{r×a}(ℂ)`: `1` for `r = 0`, and the block chart bound with all
column exponents `−2` for `r = k + 1`. -/
def blockBound (a : ℕ) : (r : ℕ) → (Fin r → Fin a → ℂ) → ℝ
  | 0, _ => 1
  | _ + 1, X => blockChartBound (fun _ : Fin a => (-2 : ℝ)) (Matrix.of X)

theorem tail_neg_two (a : ℕ) (j : Fin a) :
    ∑ l : Fin a, (if j ≤ l then (-2 : ℝ) + 1 else 0) < 0 := by
  have h1 : ∑ l : Fin a, (if j ≤ l then (-2 : ℝ) + 1 else 0) ≤
      ∑ l : Fin a, (if l = j then (-1 : ℝ) else 0) := by
    refine Finset.sum_le_sum fun l _ => ?_
    by_cases hlj : l = j
    · subst hlj
      norm_num
    · rw [ite_eq_right hlj]
      split_ifs <;> norm_num
  have h2 : ∑ l : Fin a, (if l = j then (-1 : ℝ) else 0) = -1 := by
    rw [Finset.sum_ite_eq']
    simp
  linarith

theorem integrable_blockBound (a : ℕ) : ∀ r : ℕ, Integrable (blockBound a r)
  | 0 => by
    have h : (volume : Measure (Fin 0 → Fin a → ℂ)) = Measure.dirac (fun i => i.elim0) := by
      rw [volume_pi]
      exact Measure.pi_of_empty _ _
    rw [h]
    exact integrable_const _
  | k + 1 => complexBlockChartIntegrable a (k + 1) (fun _ => -2) (tail_neg_two a)

theorem blockBound_nonneg (a : ℕ) : ∀ (r : ℕ) (X : Fin r → Fin a → ℂ), 0 ≤ blockBound a r X
  | 0, _ => zero_le_one
  | _ + 1, _ => ComplexBlockLimit.blockChartBound_nonneg _ _

theorem blockLower_zero_rows (X : Matrix (Fin 0) (Fin a) ℂ) :
    ComplexBlockParabolic.blockLower X = 1 := by
  ext i j
  refine Fin.addCases (fun p => ?_) (fun q => q.elim0) i
  refine Fin.addCases (fun p' => ?_) (fun q => q.elim0) j
  simp only [ComplexBlockParabolic.blockLower, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁, Matrix.one_apply,
    Fin.castAdd_inj]

theorem blockLowerGL_zero_rows (X : Matrix (Fin 0) (Fin a) ℂ) : blockLowerGL X = 1 := by
  apply Units.ext
  rw [ComplexBlockChart.blockLowerGL_val, blockLower_zero_rows, Units.val_one]

theorem norm_le_blockBound_succ {k : ℕ} {F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hF : NormCov (a + (k + 1)) F) {C : ℝ}
    (hC : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ‖F κ‖ ≤ C) (X : Fin (k + 1) → Fin a → ℂ)
    {κ : Langlands.GeneralLinear (a + (k + 1)) ℂ} (hκ : κ ∈ unitaryCompact ℂ (a + (k + 1))) :
    ‖F (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * κ)‖ ≤ C * blockBound a (k + 1) X := by
  set G : Langlands.GeneralLinear (a + k + 1) ℂ → ℂ := fun g => ((‖F g‖ : ℝ) : ℂ) with hG
  have hGc : ∀ g, ‖G g‖ = ‖F g‖ := fun g => by
    rw [hG, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have h := norm_le_gram (N := a + k) (F := G)
    (c := fun z => ((∏ l : Fin (a + (k + 1)), ‖(z l : ℂ)‖ ^ modExp (a + (k + 1)) l : ℝ) : ℂ))
    (σ := modExp (a + (k + 1))) (normCov_cast hF) (norm_cast_prod)
    (fun κ hκ => by rw [hGc]; exact hC κ hκ) (blockLowerGL (a := a) (k := k + 1) (Matrix.of X))
    (by rw [blockLowerGL_val]; exact gramRe_blockLower_zero _) hκ
  rw [hGc] at h
  refine h.trans ?_
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (unitaryCompact ℂ (a + (k + 1))).one_mem)
  refine mul_le_mul_of_nonneg_left (le_of_eq_of_le
    (b := (∏ l : Fin a, colGram (Matrix.of X) l ^ (-2 : ℝ)) *
      ∏ j : Fin k, rowGram (Matrix.of X) j.succ ^ (-2 : ℝ)) ?_ ?_) hC0
  · rw [Fin.prod_univ_add]
    simp only [Fin.val_castAdd, Fin.val_natAdd, blockLowerGL_val, modExp_sub]
    congr 1
    · refine Finset.prod_congr rfl fun l _ => ?_
      rw [gramRe_blockLower_col]
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [show a + (j : ℕ) + 1 = a + ((j : ℕ) + 1) by ring, gramRe_blockLower_row]
  · rw [blockBound, blockChartBound, Fin.prod_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, ite_true, one_mul]
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun j _ => ?_) fun j _ => ?_)
      (Finset.prod_nonneg fun l _ => Real.rpow_nonneg (le_trans zero_le_one
        (ComplexBlockLimit.one_le_colGram _ _)) _)
    · exact Real.rpow_nonneg (le_trans zero_le_one (ComplexBlockLimit.one_le_rowGram _ _)) _
    · rw [ite_eq_right (by omega), ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (ComplexBlockLimit.one_le_rowGram _ _) (by norm_num)

/-- **Block bound.** For norm-covariant `F` bounded by `C` on `U(a+r)`,
`‖F(n̄(X) κ)‖ ≤ C · blockBound a r X`. -/
theorem norm_le_blockBound : ∀ {r : ℕ} {F : Langlands.GeneralLinear (a + r) ℂ → ℂ},
    NormCov (a + r) F → ∀ {C : ℝ}, (∀ κ ∈ unitaryCompact ℂ (a + r), ‖F κ‖ ≤ C) →
    ∀ (X : Fin r → Fin a → ℂ) {κ : Langlands.GeneralLinear (a + r) ℂ},
      κ ∈ unitaryCompact ℂ (a + r) →
      ‖F (blockLowerGL (a := a) (k := r) (Matrix.of X) * κ)‖ ≤ C * blockBound a r X
  | 0, _, _, _, hC, X, _, hκ => by
    rw [blockLowerGL_zero_rows, one_mul, blockBound, mul_one]
    exact hC _ hκ
  | _ + 1, _, hF, _, hC, X, _, hκ => norm_le_blockBound_succ hF hC X hκ

end Block

/-! ## The chart bound -/

section Chart

variable {m : ℕ}

/-- **Chart bound.** For norm-covariant `F` bounded by `C` on `U(m+1)`,
`‖F(J(x,1) κ)‖ ≤ C ∏_l (1 + |x_l|²)^{−2}`. -/
theorem norm_le_chartBound {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ} (hF : NormCov (m + 1) F)
    {C : ℝ} (hC : ∀ κ ∈ unitaryCompact ℂ (m + 1), ‖F κ‖ ≤ C) (x : Fin m → ℂ)
    {κ : Langlands.GeneralLinear (m + 1) ℂ} (hκ : κ ∈ unitaryCompact ℂ (m + 1)) :
    ‖F (chartGL x * κ)‖ ≤ C * ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ (-2 : ℝ) := by
  set G : Langlands.GeneralLinear (m + 1) ℂ → ℂ := fun g => ((‖F g‖ : ℝ) : ℂ) with hG
  have hGc : ∀ g, ‖G g‖ = ‖F g‖ := fun g => by
    rw [hG, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have h := norm_le_chart (F := G)
    (c := fun z => ((∏ l : Fin (m + 1), ‖(z l : ℂ)‖ ^ modExp (m + 1) l : ℝ) : ℂ))
    (σ := modExp (m + 1)) (normCov_cast hF) norm_cast_prod
    (fun κ hκ => by rw [hGc]; exact hC κ hκ) x hκ
  rw [hGc] at h
  simp only [modExp_sub] at h
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (unitaryCompact ℂ (m + 1)).one_mem)
  exact h.trans (mul_le_mul_of_nonneg_left (prod_partialSq_rpow_le fun _ => by norm_num) hC0)

/-- The chart bound is integrable. -/
theorem integrable_chartBound :
    Integrable fun x : Fin m → ℂ => ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ (-2 : ℝ) :=
  integrable_prod_one_add_sq_rpow fun _ => by norm_num

end Chart


/-! ## Left multiplication on `M_{r×a}(ℂ)` -/

section LeftMul

variable {r a : ℕ}

/-- `X ↦ h X` on `M_{r×a}(ℂ) = Fin r → Fin a → ℂ`. -/
def leftMulLinearEquiv {h : Matrix (Fin r) (Fin r) ℂ} (hh : h.det ≠ 0) :
    (Fin r → Fin a → ℂ) ≃ₗ[ℂ] (Fin r → Fin a → ℂ) :=
  have hu : IsUnit h.det := isUnit_iff_ne_zero.mpr hh
  { toFun := fun X => h * Matrix.of X
    invFun := fun X => h⁻¹ * Matrix.of X
    map_add' := fun X Y => by
      change h * (Matrix.of X + Matrix.of Y) = h * Matrix.of X + h * Matrix.of Y
      rw [Matrix.mul_add]
    map_smul' := fun c X => by
      change h * (c • Matrix.of X) = c • (h * Matrix.of X)
      rw [Matrix.mul_smul]
    left_inv := fun X => by
      change h⁻¹ * (h * Matrix.of X) = Matrix.of X
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul h hu, Matrix.one_mul]
    right_inv := fun X => by
      change h * (h⁻¹ * Matrix.of X) = Matrix.of X
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv h hu, Matrix.one_mul] }

theorem leftMulLinearEquiv_apply {h : Matrix (Fin r) (Fin r) ℂ} (hh : h.det ≠ 0)
    (X : Fin r → Fin a → ℂ) : leftMulLinearEquiv hh X = h * Matrix.of X := rfl

/-- Swapping the two arguments, `M_{a×r} ≃ M_{r×a}`. -/
def swapLinearEquiv : (Fin a → Fin r → ℂ) ≃ₗ[ℂ] (Fin r → Fin a → ℂ) where
  toFun Y i j := Y j i
  invFun X j i := X i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_leftMulLinearEquiv {h : Matrix (Fin r) (Fin r) ℂ} (hh : h.det ≠ 0) :
    LinearMap.det ((leftMulLinearEquiv (a := a) hh : (Fin r → Fin a → ℂ) ≃ₗ[ℂ] _) :
      (Fin r → Fin a → ℂ) →ₗ[ℂ] (Fin r → Fin a → ℂ)) = h.det ^ a := by
  have hcomp : ((leftMulLinearEquiv (a := a) hh : (Fin r → Fin a → ℂ) ≃ₗ[ℂ] _) :
      (Fin r → Fin a → ℂ) →ₗ[ℂ] (Fin r → Fin a → ℂ)) =
      ((swapLinearEquiv : (Fin a → Fin r → ℂ) ≃ₗ[ℂ] (Fin r → Fin a → ℂ)) :
        (Fin a → Fin r → ℂ) →ₗ[ℂ] (Fin r → Fin a → ℂ)) ∘ₗ
      (LinearMap.pi fun j : Fin a => (Matrix.toLin' h).comp (LinearMap.proj j)) ∘ₗ
      ((swapLinearEquiv : (Fin a → Fin r → ℂ) ≃ₗ[ℂ] (Fin r → Fin a → ℂ)).symm :
        (Fin r → Fin a → ℂ) →ₗ[ℂ] (Fin a → Fin r → ℂ)) := by
    apply LinearMap.ext
    intro X
    funext i j
    simp [leftMulLinearEquiv, swapLinearEquiv, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hcomp, LinearMap.det_conj, LinearMap.det_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, LinearMap.det_toLin']

/-- `X ↦ h X` as a measurable equivalence. -/
def leftMulEquiv {h : Matrix (Fin r) (Fin r) ℂ} (hh : h.det ≠ 0) :
    (Fin r → Fin a → ℂ) ≃ᵐ (Fin r → Fin a → ℂ) :=
  (LinearEquiv.toContinuousLinearEquiv
    ((leftMulLinearEquiv (a := a) hh).restrictScalars ℝ)).toHomeomorph.toMeasurableEquiv

theorem leftMulEquiv_apply {h : Matrix (Fin r) (Fin r) ℂ} (hh : h.det ≠ 0)
    (X : Fin r → Fin a → ℂ) : leftMulEquiv hh X = h * Matrix.of X := rfl

theorem isAddHaarMeasure_volume_mat :
    (volume : Measure (Fin r → Fin a → ℂ)).IsAddHaarMeasure := by
  rw [volume_pi]
  exact Measure.pi.isAddHaarMeasure _

/-- Lebesgue measure on `M_{r×a}(ℂ)` transforms under `X ↦ h X` by `|det h|^{-2a}`. -/
theorem map_leftMulEquiv {h : Matrix (Fin r) (Fin r) ℂ} (hh : h.det ≠ 0) :
    Measure.map (leftMulEquiv (a := a) hh) volume =
      ENNReal.ofReal (((‖h.det‖ ^ 2) ^ a)⁻¹) • (volume : Measure (Fin r → Fin a → ℂ)) := by
  have := isAddHaarMeasure_volume_mat (r := r) (a := a)
  set Lr : (Fin r → Fin a → ℂ) ≃ₗ[ℝ] (Fin r → Fin a → ℂ) :=
    (leftMulLinearEquiv (a := a) hh).restrictScalars ℝ
  have hdet : LinearMap.det (Lr : (Fin r → Fin a → ℂ) →ₗ[ℝ] (Fin r → Fin a → ℂ)) =
      Complex.normSq h.det ^ a := by
    have := LinearMap.det_restrictScalars (R := ℝ) (S := ℂ) (A := Fin r → Fin a → ℂ)
      (f := ((leftMulLinearEquiv (a := a) hh : (Fin r → Fin a → ℂ) ≃ₗ[ℂ] _) :
        (Fin r → Fin a → ℂ) →ₗ[ℂ] (Fin r → Fin a → ℂ)))
    rw [det_leftMulLinearEquiv, map_pow, Algebra.norm_complex_apply] at this
    exact this
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin r → Fin a → ℂ)))
    (f := (Lr : (Fin r → Fin a → ℂ) →ₗ[ℝ] (Fin r → Fin a → ℂ)))
    (by rw [hdet]; exact pow_ne_zero _ (Complex.normSq_pos.mpr hh).ne')
  rw [hdet, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (sq_nonneg _) _))] at this
  exact this

theorem integral_leftMul_eq {h : Matrix (Fin r) (Fin r) ℂ} (hh : h.det ≠ 0)
    (f : (Fin r → Fin a → ℂ) → ℂ) :
    ∫ X : Fin r → Fin a → ℂ, f (h * Matrix.of X) =
      ((((‖h.det‖ ^ 2) ^ a)⁻¹ : ℝ) : ℂ) * ∫ X, f X := by
  have hm := integral_map_equiv (μ := (volume : Measure (Fin r → Fin a → ℂ)))
    (leftMulEquiv (a := a) hh) f
  rw [map_leftMulEquiv, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (sq_nonneg _) _))] at hm
  rw [show (∫ X : Fin r → Fin a → ℂ, f (h * Matrix.of X)) =
      ∫ X, f (leftMulEquiv hh X) from rfl, ← hm, Complex.real_smul]

theorem integral_leftMul_eq_real {h : Matrix (Fin r) (Fin r) ℂ} (hh : h.det ≠ 0)
    (f : (Fin r → Fin a → ℂ) → ℝ) :
    ∫ X : Fin r → Fin a → ℂ, f (h * Matrix.of X) = ((‖h.det‖ ^ 2) ^ a)⁻¹ * ∫ X, f X := by
  have hm := integral_map_equiv (μ := (volume : Measure (Fin r → Fin a → ℂ)))
    (leftMulEquiv (a := a) hh) f
  rw [map_leftMulEquiv, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (sq_nonneg _) _))] at hm
  rw [show (∫ X : Fin r → Fin a → ℂ, f (h * Matrix.of X)) =
      ∫ X, f (leftMulEquiv hh X) from rfl, ← hm, smul_eq_mul]

theorem integrable_comp_leftMul {E : Type*} [NormedAddCommGroup E]
    {h : Matrix (Fin r) (Fin r) ℂ} (hh : h.det ≠ 0) {f : (Fin r → Fin a → ℂ) → E}
    (hf : Integrable f) : Integrable fun X : Fin r → Fin a → ℂ => f (h * Matrix.of X) := by
  have h1 : Integrable f (Measure.map (leftMulEquiv (a := a) hh) volume) := by
    rw [map_leftMulEquiv]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact (integrable_map_equiv (leftMulEquiv hh) f).mp h1

end LeftMul

/-! ## Block matrices -/

section Blocks

variable {a k : ℕ}

theorem symm_castSucc_castAdd (p : Fin a) :
    (finSumFinEquiv (m := a) (n := k + 1)).symm (Fin.castAdd k p).castSucc = Sum.inl p := by
  have : ((Fin.castAdd k p).castSucc : Fin (a + (k + 1))) = Fin.castAdd (k + 1) p := Fin.ext rfl
  rw [this, finSumFinEquiv_symm_apply_castAdd]

theorem symm_castSucc_natAdd (q : Fin k) :
    (finSumFinEquiv (m := a) (n := k + 1)).symm (Fin.natAdd a q).castSucc =
      Sum.inr q.castSucc := by
  have : ((Fin.natAdd a q).castSucc : Fin (a + (k + 1))) = Fin.natAdd a q.castSucc := Fin.ext rfl
  rw [this, finSumFinEquiv_symm_apply_natAdd]

theorem symm_last :
    (finSumFinEquiv (m := a) (n := k + 1)).symm (Fin.last (a + k)) = Sum.inr (Fin.last k) := by
  have : (Fin.last (a + k) : Fin (a + (k + 1))) = Fin.natAdd a (Fin.last k) := Fin.ext rfl
  rw [this, finSumFinEquiv_symm_apply_natAdd]

/-- The rows of `X'` followed by the row `x`. -/
def rowsSnoc (X' : Fin k → Fin a → ℂ) (x : Fin a → ℂ) : Fin (k + 1) → Fin a → ℂ :=
  Fin.snoc (α := fun _ => Fin a → ℂ) X' x

theorem castAdd_ne_natAdd' (p : Fin a) (q : Fin k) :
    (Fin.castAdd k p : Fin (a + k)) ≠ Fin.natAdd a q := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem natAdd_ne_castAdd' (p : Fin a) (q : Fin k) :
    (Fin.natAdd a q : Fin (a + k)) ≠ Fin.castAdd k p := fun h => castAdd_ne_natAdd' p q h.symm

theorem last_ne_castSucc' {n : ℕ} (i : Fin n) : Fin.last n ≠ i.castSucc :=
  (Fin.castSucc_ne_last i).symm

/-- `ι(n̄(X')) = n̄([X'; 0])`. -/
theorem iota_blockLower (X' : Fin k → Fin a → ℂ) :
    iota (ComplexBlockParabolic.blockLower (Matrix.of X')) =
      ComplexBlockParabolic.blockLower (a := a) (k := k + 1) (Matrix.of (rowsSnoc X' 0)) := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
  all_goals
    try refine Fin.addCases (fun p => ?_) (fun q => ?_) i'
  all_goals
    try refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j'
  all_goals
    simp only [iota_castSucc_castSucc, iota_last_castSucc, iota_castSucc_last, iota_last_last,
      ComplexBlockParabolic.blockLower, Matrix.reindex_apply, Matrix.submatrix_apply,
      symm_castSucc_castAdd, symm_castSucc_natAdd, symm_last, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd]
  all_goals
    simp [rowsSnoc, Matrix.one_apply, last_ne_castSucc']

/-- `ι(diag(A, D)) = diag(A, ι(D))`. -/
theorem iota_blockDiag (A : Matrix (Fin a) (Fin a) ℂ) (D : Matrix (Fin k) (Fin k) ℂ) :
    iota (ComplexBlockParabolic.blockDiag A D) =
      ComplexBlockParabolic.blockDiag (a := a) (k := k + 1) A (iota D) := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
  all_goals
    try refine Fin.addCases (fun p => ?_) (fun q => ?_) i'
  all_goals
    try refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j'
  all_goals
    simp only [iota_castSucc_castSucc, iota_last_castSucc, iota_castSucc_last, iota_last_last,
      ComplexBlockParabolic.blockDiag, Matrix.reindex_apply, Matrix.submatrix_apply,
      symm_castSucc_castAdd, symm_castSucc_natAdd, symm_last, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd]
  all_goals
    simp

/-- `J((x, w), 1) = [[1, 0], [[0; x], J(w, 1)]]` in the blocks `a, k + 1`. -/
theorem Jmat_append (x : Fin a → ℂ) (w : Fin k → ℂ) :
    Jmat (Fin.snoc (Fin.append x w) 1 : Fin (a + k + 1) → ℂ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
        (1 : Matrix (Fin a) (Fin a) ℂ) 0 (Matrix.of (rowsSnoc 0 x))
        (Jmat (Fin.snoc w 1 : Fin (k + 1) → ℂ))) := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
  all_goals
    try refine Fin.addCases (fun p => ?_) (fun q => ?_) i'
  all_goals
    try refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j'
  all_goals
    simp only [Jmat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last,
      Fin.snoc_castSucc, Fin.snoc_last, Fin.append_left, Fin.append_right, Matrix.one_apply,
      Fin.castSucc_inj, Fin.castAdd_inj, Fin.natAdd_inj, castAdd_ne_natAdd', natAdd_ne_castAdd',
      Fin.castSucc_ne_last, Matrix.reindex_apply, Matrix.submatrix_apply,
      symm_castSucc_castAdd, symm_castSucc_natAdd, symm_last]
  all_goals
    simp [rowsSnoc, Matrix.one_apply]

end Blocks

/-! ## Group-level identities -/

section GroupLevel

variable {a k r : ℕ}

theorem rowsSnoc_add (X' : Fin k → Fin a → ℂ) (x : Fin a → ℂ) :
    Matrix.of (rowsSnoc X' 0) + Matrix.of (rowsSnoc 0 x) = Matrix.of (rowsSnoc X' x) := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp [rowsSnoc]

/-- `n̄([X'; x]) diag(1, J(w, 1)) = ι(n̄(X')) J((x, w), 1)`. -/
theorem blockLower_mul_blockDiag_Jmat (X' : Fin k → Fin a → ℂ) (x : Fin a → ℂ) (w : Fin k → ℂ) :
    ComplexBlockParabolic.blockLower (a := a) (k := k + 1) (Matrix.of (rowsSnoc X' x)) *
      ComplexBlockParabolic.blockDiag 1 (Jmat (Fin.snoc w 1 : Fin (k + 1) → ℂ)) =
    iota (ComplexBlockParabolic.blockLower (Matrix.of X')) *
      Jmat (Fin.snoc (Fin.append x w) 1 : Fin (a + k + 1) → ℂ) := by
  rw [iota_blockLower, Jmat_append]
  rw [ComplexBlockParabolic.blockLower, ComplexBlockParabolic.blockLower,
    ComplexBlockParabolic.blockDiag, ComplexBlockLimit.reindex_mul_reindex,
    ComplexBlockLimit.reindex_mul_reindex, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [rowsSnoc_add]

theorem iotaGL_blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (τ : Langlands.GeneralLinear k ℂ) :
    iotaGL (blockDiagGL κ₁ τ) = blockDiagGL κ₁ (iotaGL τ) := by
  apply Units.ext
  rw [iotaGL_val, ComplexBlockLimit.blockDiagGL_val, ComplexBlockLimit.blockDiagGL_val, iotaGL_val,
    iota_blockDiag]

/-- **The chart identity.**
`n̄([X'; x]) diag(κ₁, J(w, 1) ι(τ)) = ι(n̄(X')) J((x, w), 1) ι(diag(κ₁, τ))`. -/
theorem blockLowerGL_mul_blockDiagGL_chart (X' : Fin k → Fin a → ℂ) (x : Fin a → ℂ)
    (w : Fin k → ℂ) (κ₁ : Langlands.GeneralLinear a ℂ) (τ : Langlands.GeneralLinear k ℂ) :
    blockLowerGL (a := a) (k := k + 1) (Matrix.of (rowsSnoc X' x)) *
      blockDiagGL κ₁ (chartGL w * iotaGL τ) =
    iotaGL (blockLowerGL (Matrix.of X')) * chartGL (Fin.append x w) *
      iotaGL (blockDiagGL κ₁ τ) := by
  rw [iotaGL_blockDiagGL, show blockDiagGL κ₁ (chartGL w * iotaGL τ) =
    blockDiagGL 1 (chartGL w) * blockDiagGL κ₁ (iotaGL τ) by
      rw [← ComplexBlockJacquet.blockDiagGL_mul, one_mul], ← mul_assoc]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, blockLowerGL_val, ComplexBlockLimit.blockDiagGL_val, iotaGL_val,
    blockLowerGL_val, chartGL, JGL_val, chartGL, JGL_val, Units.val_one]
  exact blockLower_mul_blockDiag_Jmat X' x w

/-- `diag(1, h) n̄(X) diag(A, 1) = n̄(h X) diag(A, h)`. -/
theorem blockDiag_mul_blockLower (h : Matrix (Fin r) (Fin r) ℂ) (X : Matrix (Fin r) (Fin a) ℂ)
    (A : Matrix (Fin a) (Fin a) ℂ) :
    ComplexBlockParabolic.blockDiag 1 h * ComplexBlockParabolic.blockLower X *
        ComplexBlockParabolic.blockDiag A 1 =
      ComplexBlockParabolic.blockLower (h * X) * ComplexBlockParabolic.blockDiag A h := by
  rw [ComplexBlockParabolic.blockDiag, ComplexBlockParabolic.blockDiag,
    ComplexBlockParabolic.blockDiag, ComplexBlockParabolic.blockLower,
    ComplexBlockParabolic.blockLower, ComplexBlockLimit.reindex_mul_reindex,
    ComplexBlockLimit.reindex_mul_reindex, ComplexBlockLimit.reindex_mul_reindex,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc]

theorem blockDiagGL_mul_blockLowerGL (h : Langlands.GeneralLinear r ℂ)
    (X : Matrix (Fin r) (Fin a) ℂ) (κ : Langlands.GeneralLinear a ℂ) :
    blockDiagGL 1 h * blockLowerGL X * blockDiagGL κ 1 =
      blockLowerGL ((h : Matrix (Fin r) (Fin r) ℂ) * X) * blockDiagGL κ h := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, ComplexBlockLimit.blockDiagGL_val,
    ComplexBlockLimit.blockDiagGL_val, ComplexBlockLimit.blockDiagGL_val, blockLowerGL_val,
    blockLowerGL_val, Units.val_one, Units.val_one]
  exact blockDiag_mul_blockLower _ X _

theorem blockDiagGL_mem_unitaryCompact' {g₁ : Langlands.GeneralLinear a ℂ}
    {g₂ : Langlands.GeneralLinear r ℂ} (h₁ : g₁ ∈ unitaryCompact ℂ a)
    (h₂ : g₂ ∈ unitaryCompact ℂ r) : blockDiagGL g₁ g₂ ∈ unitaryCompact ℂ (a + r) := by
  change ((blockDiagGL g₁ g₂ : Langlands.GeneralLinear (a + r) ℂ) :
    Matrix (Fin (a + r)) (Fin (a + r)) ℂ) ∈ Matrix.unitaryGroup _ ℂ
  rw [ComplexBlockLimit.blockDiagGL_val, Matrix.mem_unitaryGroup_iff]
  have h₁' := Matrix.mem_unitaryGroup_iff.mp h₁
  have h₂' := Matrix.mem_unitaryGroup_iff.mp h₂
  rw [ComplexBlockParabolic.blockDiag, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
    ComplexBlockLimit.reindex_mul_reindex, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]
  rw [Matrix.star_eq_conjTranspose] at h₁' h₂'
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    h₁', h₂']
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem normSq_det_unitary {n : ℕ} {κ : Langlands.GeneralLinear n ℂ}
    (hκ : κ ∈ unitaryCompact ℂ n) : ‖(κ : Matrix (Fin n) (Fin n) ℂ).det‖ = 1 := by
  have h := normSqC_det_unitary ⟨κ, hκ⟩
  unfold normSqC at h
  have h2 : ‖(κ : Matrix (Fin n) (Fin n) ℂ).det‖ ^ 2 = 1 := by exact_mod_cast h
  nlinarith [norm_nonneg (κ : Matrix (Fin n) (Fin n) ℂ).det, sq_nonneg
    (‖(κ : Matrix (Fin n) (Fin n) ℂ).det‖ - 1)]

end GroupLevel

/-! ## Fubini helpers -/

section Fubini

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {ν : Measure β} {ρ : Measure γ}

/-- Integrability on `μ × ν` with `μ` finite from integrable sections with uniformly bounded
`L¹` norms. -/
theorem integrable_prod_of_bounded [IsFiniteMeasure μ] [SFinite ν] {f : α × β → ℂ}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (h1 : ∀ x, Integrable (fun y => f (x, y)) ν)
    {M : ℝ} (h2 : ∀ x, ∫ y, ‖f (x, y)‖ ∂ν ≤ M) : Integrable f (μ.prod ν) := by
  rw [integrable_prod_iff hf]
  refine ⟨ae_of_all _ h1, ?_⟩
  refine Integrable.mono' (integrable_const M) hf.norm.integral_prod_right'
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
  exact h2 x

/-- A triple integral over `μ × (ν × ρ)` as an iterated integral. -/
theorem integral_prod_prod [SFinite μ] [SFinite ν] [SFinite ρ] {f : α × (β × γ) → ℂ}
    (hf : Integrable f (μ.prod (ν.prod ρ))) :
    ∫ z, f z ∂μ.prod (ν.prod ρ) = ∫ x, ∫ y, ∫ w, f (x, (y, w)) ∂ρ ∂ν ∂μ := by
  rw [integral_prod _ hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with x hx
  exact integral_prod _ hx

end Fubini

/-! ## Rearranging `ℂ^k × M_{(k+1)×a}(ℂ)` as `M_{k×a}(ℂ) × ℂ^{a+k}` -/

section Rearrange

variable {a k : ℕ}

/-- `(X', v) ↦ (w, [X'; x])`, where `v = (x, w) ∈ ℂ^a × ℂ^k = ℂ^{a+k}`. -/
def rowsChart (a k : ℕ) :
    (Fin k → Fin a → ℂ) × (Fin (a + k) → ℂ) ≃ᵐ (Fin k → ℂ) × (Fin (k + 1) → Fin a → ℂ) :=
  ((MeasurableEquiv.refl _).prodCongr
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin (a + k) => ℂ) finSumFinEquiv).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi fun _ => ℂ))).trans
    (MeasurableEquiv.prodAssoc.symm.trans (MeasurableEquiv.prodComm.trans
      ((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.prodComm.trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Fin a → ℂ) (Fin.last k)).symm))))

theorem rowsChart_apply (X' : Fin k → Fin a → ℂ) (v : Fin (a + k) → ℂ) :
    rowsChart a k (X', v) =
      (fun q => v (Fin.natAdd a q), rowsSnoc X' fun p => v (Fin.castAdd k p)) := by
  have hE : ∀ b, (MeasurableEquiv.piCongrLeft (fun _ : Fin (a + k) => ℂ) finSumFinEquiv).symm v b =
      v (finSumFinEquiv b) := fun b => rfl
  simp [hE, Fin.snocEquiv, rowsChart, rowsSnoc, MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.piFinSuccAbove_symm_apply,
    MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi]

theorem measurePreserving_rowsChart :
    MeasurePreserving (rowsChart a k) volume volume := by
  have h1 : MeasurePreserving
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin (a + k) => ℂ) finSumFinEquiv).symm.trans
        (MeasurableEquiv.sumPiEquivProdPi fun _ => ℂ)) volume volume :=
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin k => ℂ)).comp
      (volume_measurePreserving_piCongrLeft (fun _ : Fin (a + k) => ℂ) finSumFinEquiv).symm
  have h2 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Fin a → ℂ) (Fin.last k)).symm
      volume volume :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => (volume : Measure (Fin a → ℂ)))
      (Fin.last k)).symm _
  have h3 := (MeasurePreserving.id (volume : Measure (Fin k → Fin a → ℂ))).prod h1
  have hs1 : SFinite (volume : Measure (Fin k → Fin a → ℂ)) := inferInstance
  have hs2 : SFinite (volume : Measure (Fin a → ℂ)) := inferInstance
  have hs : SFinite ((volume : Measure (Fin k → Fin a → ℂ)).prod (volume : Measure (Fin a → ℂ))) :=
    Measure.prod.instSFinite
  have h4 := (measurePreserving_prodAssoc (volume : Measure (Fin k → Fin a → ℂ))
    (volume : Measure (Fin a → ℂ)) (volume : Measure (Fin k → ℂ))).symm
  have h5 := Measure.measurePreserving_swap (μ := ((volume : Measure (Fin k → Fin a → ℂ)).prod
    (volume : Measure (Fin a → ℂ)))) (ν := (volume : Measure (Fin k → ℂ)))
  have h6 := (MeasurePreserving.id (volume : Measure (Fin k → ℂ))).prod
    (h2.comp (Measure.measurePreserving_swap (μ := (volume : Measure (Fin k → Fin a → ℂ)))
      (ν := (volume : Measure (Fin a → ℂ)))))
  exact h6.comp (h5.comp (h4.comp h3))

/-- Lebesgue integrals over `ℂ^k × M_{(k+1)×a}(ℂ)` in the coordinates `M_{k×a}(ℂ) × ℂ^{a+k}`. -/
theorem integral_rowsChart (f : (Fin k → ℂ) × (Fin (k + 1) → Fin a → ℂ) → ℂ) :
    ∫ p, f p = ∫ q, f (rowsChart a k q) :=
  (measurePreserving_rowsChart.integral_comp' f).symm

theorem integrable_rowsChart {f : (Fin k → ℂ) × (Fin (k + 1) → Fin a → ℂ) → ℂ}
    (hf : Integrable f) : Integrable fun q => f (rowsChart a k q) :=
  (measurePreserving_rowsChart.integrable_comp_emb (rowsChart a k).measurableEmbedding).mpr hf

end Rearrange

end ComplexBlockParabolicProof

open ComplexBlockParabolic in
/-- **Statement (growth along `n̄(X)` of norm-covariant functions).** Let `F : GL_{a+r}(ℂ) → ℂ`
satisfy `‖F(diag(z) u g)‖ = ∏_l |z_l|^{2(a+r−1−2l)} ‖F(g)‖` for upper unipotent `u`
(`ComplexBlockParabolicProof.NormCov`) and `‖F‖ ≤ C` on `U(a+r)`. Then there is an integrable
`B` on `M_{r×a}(ℂ) = (Fin r → Fin a → ℂ)` with `‖F(n̄(X) κ)‖ ≤ C · B(X)` for all `X` and
`κ ∈ U(a+r)`, where `n̄(X) = [[1, 0], [X, 1]]`. -/
def ComplexBlockModulusBoundStatement : Prop :=
  ∀ (a r : ℕ) (F : Langlands.GeneralLinear (a + r) ℂ → ℂ),
    ComplexBlockParabolicProof.NormCov (a + r) F →
    ∀ C : ℝ, (∀ κ ∈ unitaryCompact ℂ (a + r), ‖F κ‖ ≤ C) →
      ∃ B : (Fin r → Fin a → ℂ) → ℝ, Integrable B ∧
        ∀ (X : Fin r → Fin a → ℂ) (κ : Langlands.GeneralLinear (a + r) ℂ),
          κ ∈ unitaryCompact ℂ (a + r) →
            ‖F (blockLowerGL (Matrix.of X) * κ)‖ ≤ C * B X

theorem complexBlockModulusBound : ComplexBlockModulusBoundStatement :=
  fun a r _ hF _ hC => ⟨ComplexBlockParabolicProof.blockBound a r,
    ComplexBlockParabolicProof.integrable_blockBound a r,
    fun X _ hκ => ComplexBlockParabolicProof.norm_le_blockBound hF hC X hκ⟩

end Langlands.Archimedean
