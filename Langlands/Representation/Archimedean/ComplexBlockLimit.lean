import Langlands.Representation.Archimedean.ComplexBlockChartBound
import Langlands.Representation.Archimedean.ComplexJacquetLimit
import Langlands.Representation.Archimedean.ComplexPartialSqIntegral

/-!
# The limit argument along the maximal parabolic subgroup `P_{a,k+1}` of `GL_{a+k+1}(ℂ)`

Let `u` lie in the principal series of `χ⁻¹` and `h` in that of `χ` on `GL_{a+k+1}(ℂ)`, where the
last `k+1` exponents of `χ` are tied and strictly below the earlier ones. If
`∫_{U(a+k+1)} u(κ g) h(κ) dκ = 0` for every `g`, then
`∫_{U(a)} ∫_{U(k+1)} u(diag(κ₁, κ₂)) ∫_X h(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁ = 0`
(`ComplexBlockLimit.integral_mul_blockStep_eq_zero`), assuming the block integration formula
`ComplexBlockParabolicIntegrationStatement` and the integrability statement
`ComplexBlockChartIntegrableStatement`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix ComplexOrder

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexBlockLimit

open ComplexBlockParabolic ComplexBlockChart Langlands.GeneralLinear

/-! ## Determinants of `1 + c A` for positive semidefinite `A` -/

section Det

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_one_add_smul_eq_prod {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (c : ℝ) :
    (1 + (c : ℂ) • A).det = ∏ i, ((1 + c * hA.1.eigenvalues i : ℝ) : ℂ) := by
  have hspec := hA.1.spectral_theorem
  set U := hA.1.eigenvectorUnitary
  have hUU : (U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  have h1 : 1 + (c : ℂ) • A = (U : Matrix ι ι ℂ) *
      (1 + (c : ℂ) • diagonal (RCLike.ofReal ∘ hA.1.eigenvalues)) * star (U : Matrix ι ι ℂ) := by
    conv_lhs => rw [hspec]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, Matrix.mul_smul, Matrix.smul_mul]
  have hdetU : (U : Matrix ι ι ℂ).det * (star (U : Matrix ι ι ℂ)).det = 1 := by
    rw [← Matrix.det_mul, hUU, Matrix.det_one]
  rw [h1, Matrix.det_mul, Matrix.det_mul]
  have hre : ∀ X : ℂ, (U : Matrix ι ι ℂ).det * X * (star (U : Matrix ι ι ℂ)).det =
      X * ((U : Matrix ι ι ℂ).det * (star (U : Matrix ι ι ℂ)).det) := fun X => by ring
  rw [hre, hdetU, mul_one]
  have hdiag : 1 + (c : ℂ) • diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) =
      diagonal fun i => ((1 + c * hA.1.eigenvalues i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Matrix.one_apply_ne hij]
  rw [hdiag, Matrix.det_diagonal]

theorem re_det_one_add_smul {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (c : ℝ) :
    ((1 + (c : ℂ) • A).det).re = ∏ i, (1 + c * hA.1.eigenvalues i) := by
  rw [det_one_add_smul_eq_prod hA, ← Complex.ofReal_prod, Complex.ofReal_re]

theorem one_le_re_det {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    1 ≤ ((1 + (c : ℂ) • A).det).re := by
  rw [re_det_one_add_smul hA]
  have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : ι => (1 : ℝ))
    (g := fun i => 1 + c * hA.1.eigenvalues i) (fun _ _ => zero_le_one)
    (fun i _ => by have := hA.eigenvalues_nonneg i; nlinarith)
  simpa using h

theorem re_det_mono {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) :
    ((1 + (c : ℂ) • A).det).re ≤ ((1 + (d : ℂ) • A).det).re := by
  rw [re_det_one_add_smul hA, re_det_one_add_smul hA]
  exact Finset.prod_le_prod₀ (fun i _ => by have := hA.eigenvalues_nonneg i; nlinarith)
    (fun i _ => by have := hA.eigenvalues_nonneg i; nlinarith)

end Det

/-! ## Scaling the block chart -/

section Scaling

variable {a k : ℕ}

theorem colGram_smul (X : Matrix (Fin k) (Fin a) ℂ) (t : ℝ) (l : Fin a) :
    colGram (((t : ℂ)) • X) l =
      ((1 + ((t ^ 2 : ℝ) : ℂ) • ((colsUpTo X l)ᴴ * colsUpTo X l)).det).re := by
  rw [colGram]
  congr 3
  ext p q
  simp only [colsUpTo, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul, id, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem rowGram_smul (X : Matrix (Fin k) (Fin a) ℂ) (t : ℝ) (j : Fin k) :
    rowGram (((t : ℂ)) • X) j =
      ((1 + ((t ^ 2 : ℝ) : ℂ) • (rowsFrom X j * (rowsFrom X j)ᴴ)).det).re := by
  rw [rowGram]
  congr 3
  ext p q
  simp only [rowsFrom, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul, id, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem colGram_eq (X : Matrix (Fin k) (Fin a) ℂ) (l : Fin a) :
    colGram X l = ((1 + ((1 : ℝ) : ℂ) • ((colsUpTo X l)ᴴ * colsUpTo X l)).det).re := by
  simpa using colGram_smul X 1 l

theorem rowGram_eq (X : Matrix (Fin k) (Fin a) ℂ) (j : Fin k) :
    rowGram X j = ((1 + ((1 : ℝ) : ℂ) • (rowsFrom X j * (rowsFrom X j)ᴴ)).det).re := by
  simpa using rowGram_smul X 1 j

theorem one_le_colGram (X : Matrix (Fin k) (Fin a) ℂ) (l : Fin a) : 1 ≤ colGram X l := by
  rw [colGram_eq]
  exact one_le_re_det (Matrix.posSemidef_conjTranspose_mul_self _) zero_le_one

theorem one_le_rowGram (X : Matrix (Fin k) (Fin a) ℂ) (j : Fin k) : 1 ≤ rowGram X j := by
  rw [rowGram_eq]
  exact one_le_re_det (Matrix.posSemidef_self_mul_conjTranspose _) zero_le_one

theorem colGram_smul_le (X : Matrix (Fin k) (Fin a) ℂ) {t : ℝ} (ht : |t| ≤ 1) (l : Fin a) :
    colGram (((t : ℂ)) • X) l ≤ colGram X l := by
  rw [colGram_smul, colGram_eq]
  refine re_det_mono (Matrix.posSemidef_conjTranspose_mul_self _) (sq_nonneg t) ?_
  rw [← sq_abs]
  nlinarith [abs_nonneg t]

theorem rowGram_smul_le (X : Matrix (Fin k) (Fin a) ℂ) {t : ℝ} (ht : |t| ≤ 1) (j : Fin k) :
    rowGram (((t : ℂ)) • X) j ≤ rowGram X j := by
  rw [rowGram_smul, rowGram_eq]
  refine re_det_mono (Matrix.posSemidef_self_mul_conjTranspose _) (sq_nonneg t) ?_
  rw [← sq_abs]
  nlinarith [abs_nonneg t]

theorem blockChartBound_nonneg (ε : Fin a → ℝ) (X : Matrix (Fin k) (Fin a) ℂ) :
    0 ≤ blockChartBound ε X := by
  refine mul_nonneg (Finset.prod_nonneg fun l _ => Real.rpow_nonneg
    (le_trans zero_le_one (one_le_colGram X l)) _) (Finset.prod_nonneg fun j _ => ?_)
  split_ifs
  · exact zero_le_one
  · exact inv_nonneg.mpr (le_trans zero_le_one (one_le_rowGram X j))

/-- **Domination.** For dual exponents `ε^u + ε^h = −2` and `|t| ≤ 1`,
`B_{ε^u}(t X) B_{ε^h}(X) ≤ B_{max(ε^h, −2)}(X)`. -/
theorem blockChartBound_mul_le {εu εh : Fin a → ℝ} (hsum : ∀ l, εu l + εh l = -2)
    (X : Matrix (Fin k) (Fin a) ℂ) {t : ℝ} (ht : |t| ≤ 1) :
    blockChartBound εu (((t : ℂ)) • X) * blockChartBound εh X ≤
      blockChartBound (fun l => max (εh l) (-2)) X := by
  unfold blockChartBound
  rw [show ∀ p q r w : ℝ, p * q * (r * w) = (p * r) * (q * w) from fun _ _ _ _ => by ring,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun l _ => mul_nonneg (Real.rpow_nonneg
    (le_trans zero_le_one (one_le_colGram _ l)) _) (Real.rpow_nonneg
    (le_trans zero_le_one (one_le_colGram _ l)) _)) fun l _ => ?_)
    (Finset.prod_le_prod₀ (fun j _ => ?_) fun j _ => ?_) (Finset.prod_nonneg fun j _ => ?_)
    (Finset.prod_nonneg fun l _ => Real.rpow_nonneg
      (le_trans zero_le_one (one_le_colGram _ l)) _)
  · have h1 := one_le_colGram X l
    have h1t := one_le_colGram (((t : ℂ)) • X) l
    have hle := colGram_smul_le X ht l
    by_cases hu : 0 ≤ εu l
    · calc colGram (((t : ℂ)) • X) l ^ εu l * colGram X l ^ εh l
          ≤ colGram X l ^ εu l * colGram X l ^ εh l :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) hle hu)
              (Real.rpow_nonneg (by linarith) _)
        _ = colGram X l ^ (-2 : ℝ) := by
            rw [← Real.rpow_add (by linarith), hsum]
        _ ≤ colGram X l ^ max (εh l) (-2) :=
            Real.rpow_le_rpow_of_exponent_le h1 (le_max_right _ _)
    · calc colGram (((t : ℂ)) • X) l ^ εu l * colGram X l ^ εh l
          ≤ 1 * colGram X l ^ εh l :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos h1t (by linarith))
              (Real.rpow_nonneg (by linarith) _)
        _ ≤ colGram X l ^ max (εh l) (-2) := by
            rw [one_mul]
            exact Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)
  · split_ifs
    · norm_num
    · exact mul_nonneg (inv_nonneg.mpr (le_trans zero_le_one (one_le_rowGram _ j)))
        (inv_nonneg.mpr (le_trans zero_le_one (one_le_rowGram _ j)))
  · split_ifs
    · norm_num
    · have h1t := one_le_rowGram (((t : ℂ)) • X) j
      calc (rowGram (((t : ℂ)) • X) j)⁻¹ * (rowGram X j)⁻¹ ≤ 1 * (rowGram X j)⁻¹ :=
            mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ h1t)
              (inv_nonneg.mpr (le_trans zero_le_one (one_le_rowGram _ j)))
        _ = (rowGram X j)⁻¹ := one_mul _
  · split_ifs
    · norm_num
    · exact mul_nonneg (inv_nonneg.mpr (le_trans zero_le_one (one_le_rowGram _ j)))
        (inv_nonneg.mpr (le_trans zero_le_one (one_le_rowGram _ j)))

end Scaling

/-! ## The central element `d(s) = diag(1_a, s·1_k)` -/

section Central

variable {a k : ℕ}

theorem reindex_mul_reindex (M N : Matrix (Fin a ⊕ Fin k) (Fin a ⊕ Fin k) ℂ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv M * Matrix.reindex finSumFinEquiv finSumFinEquiv N =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (M * N) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.reindex_apply]

/-- The matrix `diag(1_a, s·1_k)`. -/
def tailMat (s : ℂ) : Matrix (Fin (a + k)) (Fin (a + k)) ℂ :=
  ComplexBlockParabolic.blockDiag (1 : Matrix (Fin a) (Fin a) ℂ) (s • (1 : Matrix (Fin k) (Fin k) ℂ))

/-- The diagonal entries of `d(s) = diag(1_a, s·1_k)`. -/
def tailEntries (s : ℂˣ) : Fin (a + k) → ℂˣ := fun i => if (i : ℕ) < a then 1 else s

/-- `d(s) = diag(1_a, s·1_k)`. -/
def dTail (s : ℂˣ) : Langlands.GeneralLinear (a + k) ℂ :=
  Iwasawa.diagonalUnits (tailEntries (a := a) (k := k) s)

theorem dTail_val (s : ℂˣ) :
    ((dTail (a := a) (k := k) s : Langlands.GeneralLinear (a + k) ℂ) :
      Matrix (Fin (a + k)) (Fin (a + k)) ℂ) = tailMat (s : ℂ) := by
  rw [dTail, Iwasawa.diagonalUnits_val, tailMat, ComplexBlockParabolic.blockDiag]
  ext i j
  refine Fin.addCases (fun p => ?_) (fun q => ?_) i <;>
    refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j <;>
    simp [tailEntries, Matrix.diagonal_apply, Matrix.one_apply, Fin.castAdd_inj, Fin.natAdd_inj]
  all_goals
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega

theorem blockLower_mul_blockDiag_tail (X : Matrix (Fin k) (Fin a) ℂ) {s : ℂ} (hs : s ≠ 0) :
    blockLower X * tailMat s = tailMat s * blockLower (s⁻¹ • X) := by
  rw [blockLower, blockLower, tailMat, ComplexBlockParabolic.blockDiag, reindex_mul_reindex, reindex_mul_reindex,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1
  simp [smul_smul, hs]

theorem blockDiag_mul_blockDiag_tail (A : Matrix (Fin a) (Fin a) ℂ) (D : Matrix (Fin k) (Fin k) ℂ)
    (s : ℂ) : ComplexBlockParabolic.blockDiag A D * tailMat s =
      tailMat s * ComplexBlockParabolic.blockDiag A D := by
  rw [ComplexBlockParabolic.blockDiag, tailMat, ComplexBlockParabolic.blockDiag, reindex_mul_reindex, reindex_mul_reindex, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

theorem blockLowerGL_mul_dTail (X : Matrix (Fin k) (Fin a) ℂ) (s : ℂˣ) :
    blockLowerGL X * dTail s = dTail s * blockLowerGL ((s : ℂ)⁻¹ • X) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ComplexBlockChart.blockLowerGL_val,
    ComplexBlockChart.blockLowerGL_val, dTail_val]
  exact blockLower_mul_blockDiag_tail X s.ne_zero

theorem blockDiagGL_val (g₁ : Langlands.GeneralLinear a ℂ) (g₂ : Langlands.GeneralLinear k ℂ) :
    ((blockDiagGL g₁ g₂ : Langlands.GeneralLinear (a + k) ℂ) :
      Matrix (Fin (a + k)) (Fin (a + k)) ℂ) =
      ComplexBlockParabolic.blockDiag (g₁ : Matrix (Fin a) (Fin a) ℂ) (g₂ : Matrix (Fin k) (Fin k) ℂ) :=
  IsUnit.unit_spec _

theorem blockDiagGL_mul_dTail (g₁ : Langlands.GeneralLinear a ℂ)
    (g₂ : Langlands.GeneralLinear k ℂ) (s : ℂˣ) :
    blockDiagGL g₁ g₂ * dTail s = dTail s * blockDiagGL g₁ g₂ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, blockDiagGL_val, dTail_val]
  exact blockDiag_mul_blockDiag_tail _ _ _

theorem blockLower_mul_blockLower_neg (X : Matrix (Fin k) (Fin a) ℂ) :
    blockLower X * blockLower (-X) = 1 := by
  rw [blockLower, blockLower, reindex_mul_reindex, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, add_neg_cancel]
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem continuous_blockLower : Continuous fun X : Matrix (Fin k) (Fin a) ℂ => blockLower X :=
  (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_id
    continuous_const).matrix_reindex _ _

theorem continuous_blockLowerGL :
    Continuous fun X : Matrix (Fin k) (Fin a) ℂ => blockLowerGL X := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact continuous_blockLower.congr fun X => (ComplexBlockChart.blockLowerGL_val X).symm
  · have h : ∀ X : Matrix (Fin k) (Fin a) ℂ,
        (((blockLowerGL X)⁻¹ : Langlands.GeneralLinear (a + k) ℂ) :
          Matrix (Fin (a + k)) (Fin (a + k)) ℂ) = blockLower (-X) := fun X => by
      have h1 : blockLowerGL X * blockLowerGL (-X) = 1 := by
        apply Units.ext
        rw [Units.val_mul, ComplexBlockChart.blockLowerGL_val, ComplexBlockChart.blockLowerGL_val,
          blockLower_mul_blockLower_neg, Units.val_one]
      rw [inv_eq_of_mul_eq_one_right h1, ComplexBlockChart.blockLowerGL_val]
    exact (continuous_blockLower.comp continuous_neg).congr fun X => (h X).symm

theorem blockLowerGL_zero : blockLowerGL (0 : Matrix (Fin k) (Fin a) ℂ) = 1 := by
  apply Units.ext
  rw [ComplexBlockChart.blockLowerGL_val, Units.val_one, blockLower, Matrix.fromBlocks_one,
    Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem continuous_blockDiagGL :
    Continuous fun p : Langlands.GeneralLinear a ℂ × Langlands.GeneralLinear k ℂ =>
      blockDiagGL p.1 p.2 := by
  rw [Units.continuous_iff]
  have hval : ∀ p : Langlands.GeneralLinear a ℂ × Langlands.GeneralLinear k ℂ,
      ((blockDiagGL p.1 p.2 : Langlands.GeneralLinear (a + k) ℂ) :
        Matrix (Fin (a + k)) (Fin (a + k)) ℂ) =
      ComplexBlockParabolic.blockDiag (p.1 : Matrix (Fin a) (Fin a) ℂ)
        (p.2 : Matrix (Fin k) (Fin k) ℂ) := fun p => blockDiagGL_val _ _
  have hinv : ∀ p : Langlands.GeneralLinear a ℂ × Langlands.GeneralLinear k ℂ,
      (((blockDiagGL p.1 p.2)⁻¹ : Langlands.GeneralLinear (a + k) ℂ) :
        Matrix (Fin (a + k)) (Fin (a + k)) ℂ) =
      ComplexBlockParabolic.blockDiag ((p.1⁻¹ : Langlands.GeneralLinear a ℂ) :
        Matrix (Fin a) (Fin a) ℂ) ((p.2⁻¹ : Langlands.GeneralLinear k ℂ) :
          Matrix (Fin k) (Fin k) ℂ) := fun p => by
    have h1 : blockDiagGL p.1 p.2 * blockDiagGL p.1⁻¹ p.2⁻¹ = 1 := by
      apply Units.ext
      rw [Units.val_mul, blockDiagGL_val, blockDiagGL_val, ComplexBlockParabolic.blockDiag,
        ComplexBlockParabolic.blockDiag, reindex_mul_reindex, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Units.mul_inv,
        Units.val_one]
      rw [Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
    rw [inv_eq_of_mul_eq_one_right h1, blockDiagGL_val]
  refine ⟨?_, ?_⟩
  · exact ((Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst)
      continuous_const continuous_const (Units.continuous_val.comp continuous_snd)).matrix_reindex
      _ _).congr fun p => (hval p).symm
  · exact ((Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst)
      continuous_const continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _).congr
      fun p => (hinv p).symm

end Central

/-! ## Bounds for tied phase-power principal series -/

section Bounds

open ComplexPartialJacquet

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- The block chart bound for a principal series of phase-power characters whose exponents at the
positions `a, …, a+k` have equal real parts. -/
theorem norm_le_block (hχ : IsPhasePower χ e) (htie : ∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re)
    {h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ} (hh : h ∈ principalSeries ℂ (a + (k + 1)) χ)
    {C : ℝ} (hC : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ‖h κ‖ ≤ C)
    (X : Matrix (Fin (k + 1)) (Fin a) ℂ) {κ : Langlands.GeneralLinear (a + (k + 1)) ℂ}
    (hκ : κ ∈ unitaryCompact ℂ (a + (k + 1))) :
    ‖h (blockLowerGL (a := a) (k := k + 1) X * κ)‖ ≤
      C * blockChartBound (fun l : Fin a => (e ((l : ℕ) + 1)).re - (e l).re - 1) X := by
  set σ : ℕ → ℝ := fun l => 2 * ((e l).re + (((a + (k + 1) : ℕ) : ℝ) - 1) / 2 - (l : ℝ))
    with hσdef
  have hσ : ∀ j : ℕ, 1 ≤ j → j ≤ k → (σ (a + j) - σ (a + j - 1)) / 2 = -1 := by
    intro j hj1 hjk
    simp only [hσdef]
    have h1 : (e (a + j)).re = (e a).re := htie j hjk
    have h2 : (e (a + j - 1)).re = (e a).re := by
      rw [show a + j - 1 = a + (j - 1) by omega]
      exact htie (j - 1) (by omega)
    rw [h1, h2, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hb := ComplexBlockChart.norm_le_blockChartBound (σ := σ) hh.2
    (fun z => norm_principalSeriesCharacter hχ _ z) hC hσ X hκ
  have hexp : (fun l : Fin a => (σ ((l : ℕ) + 1) - σ l) / 2) =
      fun l : Fin a => (e ((l : ℕ) + 1)).re - (e l).re - 1 := by
    funext l
    simp only [hσdef]
    push_cast
    ring
  rwa [hexp] at hb

theorem blockDiagGL_mem_unitaryCompact {g₁ : Langlands.GeneralLinear a ℂ}
    {g₂ : Langlands.GeneralLinear (k + 1) ℂ} (h₁ : g₁ ∈ unitaryCompact ℂ a)
    (h₂ : g₂ ∈ unitaryCompact ℂ (k + 1)) :
    blockDiagGL g₁ g₂ ∈ unitaryCompact ℂ (a + (k + 1)) := by
  change ((blockDiagGL g₁ g₂ : Langlands.GeneralLinear (a + (k + 1)) ℂ) :
    Matrix (Fin (a + (k + 1))) (Fin (a + (k + 1))) ℂ) ∈ Matrix.unitaryGroup _ ℂ
  rw [blockDiagGL_val, Matrix.mem_unitaryGroup_iff]
  have h₁' := Matrix.mem_unitaryGroup_iff.mp h₁
  have h₂' := Matrix.mem_unitaryGroup_iff.mp h₂
  rw [ComplexBlockParabolic.blockDiag, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
    reindex_mul_reindex, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  rw [Matrix.star_eq_conjTranspose] at h₁' h₂'
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    h₁', h₂']
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

/-- The tail condition for the dominating exponents `max(Re e_{l+1} − Re e_l − 1, −2)`. -/
theorem tail_max (hord : ∀ l : ℕ, l < a → (e (l + 1)).re ≤ (e l).re)
    (hgap : ∀ l : ℕ, l + 1 = a → (e (l + 1)).re < (e l).re) :
    ∀ j : Fin a, ∑ l : Fin a, (if j ≤ l then
      max ((e ((l : ℕ) + 1)).re - (e l).re - 1) (-2) + 1 else 0) < 0 := by
  cases a with
  | zero => intro j; exact j.elim0
  | succ m =>
    have h := ComplexPartialSqIntegral.tailCondition_of_le
      (γ := fun l : Fin (m + 1) => max ((e ((l : ℕ) + 1)).re - (e l).re - 1) (-2))
      (fun l => max_le (by linarith [hord l l.isLt]) (by norm_num))
      (max_lt (by have := hgap m rfl; simp only [Fin.val_last]; linarith) (by norm_num))
    intro j
    simpa using h j

end Bounds

/-! ## The pairing identity -/

section Pairing

open ComplexPartialJacquet ComplexJacquetLimit ComplexDuality ComplexKIntegralInvariance

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- The integrand `u(n̄(s⁻¹X) diag(κ₁,κ₂)) h(n̄(X) diag(κ₁,κ₂))` of the limit argument. -/
def Φ (u h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) (s : ℝ)
    (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ (k + 1)) (X : Fin (k + 1) → Fin a → ℂ) : ℂ :=
  u (blockLowerGL (a := a) (k := k + 1) (((s⁻¹ : ℝ) : ℂ) • Matrix.of X) *
      blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) *
    h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
      blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))

theorem integral_Φ_eq_zero (hT3 : ComplexBlockParabolicIntegrationStatement)
    (hχ : IsPhasePower χ e) {u h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : u ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (hh : h ∈ principalSeries ℂ (a + (k + 1)) χ)
    (h0 : ∀ g : Langlands.GeneralLinear (a + (k + 1)) ℂ,
      ∫ κ, u ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) * g) * h κ
        ∂unitaryHaar (a + (k + 1)) = 0)
    {s : ℝ} (hs : 0 < s) :
    ∫ κ₁ : unitaryCompact ℂ a, (∫ κ₂ : unitaryCompact ℂ (k + 1),
      (∫ X : Fin (k + 1) → Fin a → ℂ, Φ u h s κ₁ κ₂ X) ∂unitaryHaar (k + 1)) ∂unitaryHaar a = 0 := by
  obtain ⟨c, hc, hT3'⟩ := hT3 a (k + 1)
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set s' : ℂˣ := Units.mk0 (s : ℂ) hs0 with hs'
  set d : Langlands.GeneralLinear (a + (k + 1)) ℂ := dTail (a := a) (k := k + 1) s' with hd
  have hud := rightTranslation_mem_principalSeries (χ := dualChar χ) hu d
  set F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ := fun y => u (y * d) * h y with hFdef
  have hF : F ∈ principalSeries ℂ (a + (k + 1)) (modulusCharacter (a + (k + 1))) := by
    refine ⟨contMDiff_mul_fun hud.1 hh.1, fun z v y => ?_⟩
    simp only [hFdef]
    rw [mul_assoc _ y, hu.2 z v, hh.2 z v y, ← principalSeriesCharacter_dual_mul hχ]
    ring
  have h1 := (hT3' F hF).2
  rw [show (∫ κ, F (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) ∂unitaryHaar (a + (k + 1))) = 0
    from h0 d] at h1
  set c' := principalSeriesCharacter ℂ (a + (k + 1)) (dualChar χ) (tailEntries s') with hc'def
  have hdu : ∀ y, u (d * y) = c' * u y := fun y => by
    have := hu.2 (tailEntries s') 1 y
    simpa [hd, dTail] using this
  have hpt : ∀ (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ (k + 1))
      (X : Fin (k + 1) → Fin a → ℂ),
      F (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
        blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) =
        c' * Φ u h s κ₁ κ₂ X := by
    intro κ₁ κ₂ X
    simp only [hFdef, Φ]
    rw [mul_assoc, blockDiagGL_mul_dTail, ← mul_assoc, blockLowerGL_mul_dTail, mul_assoc, hdu]
    have : ((s' : ℂ))⁻¹ • Matrix.of X = ((s⁻¹ : ℝ) : ℂ) • Matrix.of X := by
      rw [hs', Units.val_mk0, Complex.ofReal_inv]
    rw [this]
    ring
  simp_rw [hpt, integral_const_mul] at h1
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hc'0 : c' ≠ 0 := by
    rw [← norm_ne_zero_iff, hc'def, norm_principalSeriesCharacter hχ.dual]
    exact (Finset.prod_pos fun l _ =>
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (Units.ne_zero _)) _).ne'
  have h2 := h1.symm
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hc0
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hc'0
    · exact h4

end Pairing

/-! ## Domination and the limit -/

section Limit

open ComplexPartialJacquet ComplexJacquetLimit ComplexDuality ComplexKIntegralInvariance

open scoped Manifold ContDiff Matrix.Norms.Operator

variable {a k : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- `U(n)` is second countable (it carries the topology induced from `M_n(ℂ) × M_n(ℂ)ᵐᵒᵖ`). -/
instance secondCountableTopology_unitaryCompact (n : ℕ) :
    SecondCountableTopology (unitaryCompact ℂ n) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    TopologicalSpace.secondCountableTopology_induced _ (Matrix (Fin n) (Fin n) ℂ) MulOpposite.unop
  have : SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
    TopologicalSpace.secondCountableTopology_induced _ _
      (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ))
  exact TopologicalSpace.secondCountableTopology_induced (unitaryCompact ℂ n)
    (Langlands.GeneralLinear n ℂ) Subtype.val

theorem continuous_Φ {T : Type*} [TopologicalSpace T]
    {u h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ} (hu : Continuous u)
    (hh : Continuous h) (s : ℝ) {f₁ : T → unitaryCompact ℂ a} {f₂ : T → unitaryCompact ℂ (k + 1)}
    {fX : T → Fin (k + 1) → Fin a → ℂ} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hfX : Continuous fX) :
    Continuous fun t => Φ u h s (f₁ t) (f₂ t) (fX t) := by
  have hd : Continuous fun t =>
      blockDiagGL (a := a) (k := k + 1) ((f₁ t : unitaryCompact ℂ a) : Langlands.GeneralLinear a ℂ)
        ((f₂ t : unitaryCompact ℂ (k + 1)) : Langlands.GeneralLinear (k + 1) ℂ) :=
    continuous_blockDiagGL.comp ((continuous_subtype_val.comp hf₁).prodMk
      (continuous_subtype_val.comp hf₂))
  have hX : Continuous fun t => blockLowerGL (a := a) (k := k + 1) (Matrix.of (fX t)) :=
    continuous_blockLowerGL.comp hfX
  have hXs : Continuous fun t =>
      blockLowerGL (a := a) (k := k + 1) (((s⁻¹ : ℝ) : ℂ) • Matrix.of (fX t)) :=
    (continuous_blockLowerGL.comp (continuous_const_smul (((s⁻¹ : ℝ) : ℂ)))).comp hfX
  exact (hu.comp (hXs.mul hd)).mul (hh.comp (hX.mul hd))

/-- **Domination.** For `s ≥ 1`, `‖Φ_s(κ₁, κ₂, X)‖ ≤ C_u C_h B_γ(X)` with
`γ_l = max(Re e_{l+1} − Re e_l − 1, −2)`. -/
theorem norm_Φ_le (hχ : IsPhasePower χ e) (htie : ∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re)
    {u h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : u ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (hh : h ∈ principalSeries ℂ (a + (k + 1)) χ)
    {Cu Ch : ℝ} (hCu : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ‖u κ‖ ≤ Cu)
    (hCh : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ‖h κ‖ ≤ Ch)
    {s : ℝ} (hs : 1 ≤ s) (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ (k + 1))
    (X : Fin (k + 1) → Fin a → ℂ) :
    ‖Φ u h s κ₁ κ₂ X‖ ≤ Cu * Ch * blockChartBound
      (fun l : Fin a => max ((e ((l : ℕ) + 1)).re - (e l).re - 1) (-2)) (Matrix.of X) := by
  have hκ := blockDiagGL_mem_unitaryCompact κ₁.2 κ₂.2
  have hCu0 : 0 ≤ Cu := le_trans (norm_nonneg _) (hCu 1 (unitaryCompact ℂ _).one_mem)
  have hCh0 : 0 ≤ Ch := le_trans (norm_nonneg _) (hCh 1 (unitaryCompact ℂ _).one_mem)
  have htie' : ∀ j : ℕ, j ≤ k → ((fun l => -e l) (a + j)).re = ((fun l => -e l) a).re := by
    intro j hj
    simp only [Complex.neg_re, htie j hj]
  set εu : Fin a → ℝ := fun l => (-e ((l : ℕ) + 1)).re - (-e l).re - 1 with hεu
  set εh : Fin a → ℝ := fun l => (e ((l : ℕ) + 1)).re - (e l).re - 1 with hεh
  have h1 : ‖u (blockLowerGL (a := a) (k := k + 1) (((s⁻¹ : ℝ) : ℂ) • Matrix.of X) *
      blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))‖ ≤
      Cu * blockChartBound εu (((s⁻¹ : ℝ) : ℂ) • Matrix.of X) :=
    norm_le_block hχ.dual htie' hu hCu _ hκ
  have h2 : ‖h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
      blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))‖ ≤
      Ch * blockChartBound εh (Matrix.of X) :=
    norm_le_block hχ htie hh hCh _ hκ
  have hsum : ∀ l : Fin a, εu l + εh l = -2 := by
    intro l
    simp only [hεu, hεh, Complex.neg_re]
    ring
  have ht : |s⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_le_one_of_one_le₀ hs
  have hd := blockChartBound_mul_le hsum (Matrix.of X) ht
  unfold Φ
  rw [norm_mul]
  calc _ ≤ (Cu * blockChartBound εu (((s⁻¹ : ℝ) : ℂ) • Matrix.of X)) *
        (Ch * blockChartBound εh (Matrix.of X)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hCu0 (blockChartBound_nonneg _ _))
    _ = Cu * Ch * (blockChartBound εu (((s⁻¹ : ℝ) : ℂ) • Matrix.of X) *
        blockChartBound εh (Matrix.of X)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (mul_nonneg hCu0 hCh0)

/-- **The limit argument along `P_{a,k+1}`.** Let `χ` be phase-power characters with exponents `e`
such that `Re e_a = ⋯ = Re e_{a+k}`, `Re e_{l+1} ≤ Re e_l` for `l < a` and `Re e_a < Re e_{a−1}`;
let `u` lie in the principal series of `χ⁻¹` and `h` in that of `χ` on `GL_{a+k+1}(ℂ)`. If
`∫_{U(a+k+1)} u(κ g) h(κ) dκ = 0` for every `g`, then
`∫_{U(a)} ∫_{U(k+1)} u(diag(κ₁, κ₂)) ∫_X h(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁ = 0`, assuming the
statements `ComplexBlockChartIntegrableStatement` and `ComplexBlockParabolicIntegrationStatement`. -/
theorem integral_mul_blockStep_eq_zero (hT1 : ComplexBlockChartIntegrableStatement)
    (hT3 : ComplexBlockParabolicIntegrationStatement)
    (hχ : IsPhasePower χ e) (htie : ∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re)
    (hord : ∀ l : ℕ, l < a → (e (l + 1)).re ≤ (e l).re)
    (hgap : ∀ l : ℕ, l + 1 = a → (e (l + 1)).re < (e l).re)
    {u h : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hu : u ∈ principalSeries ℂ (a + (k + 1)) (dualChar χ))
    (hh : h ∈ principalSeries ℂ (a + (k + 1)) χ)
    (h0 : ∀ g : Langlands.GeneralLinear (a + (k + 1)) ℂ,
      ∫ κ, u ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) * g) * h κ
        ∂unitaryHaar (a + (k + 1)) = 0) :
    ∫ κ₁ : unitaryCompact ℂ a, (∫ κ₂ : unitaryCompact ℂ (k + 1),
      u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) *
        (∫ X : Fin (k + 1) → Fin a → ℂ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
          blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)))
      ∂unitaryHaar (k + 1)) ∂unitaryHaar a = 0 := by
  obtain ⟨Cu, hCu⟩ := exists_bound_unitaryCompact hu.1.continuous
  obtain ⟨Ch, hCh⟩ := exists_bound_unitaryCompact hh.1.continuous
  set γ : Fin a → ℝ := fun l => max ((e ((l : ℕ) + 1)).re - (e l).re - 1) (-2) with hγ
  set D : (Fin (k + 1) → Fin a → ℂ) → ℝ := fun X => Cu * Ch * blockChartBound γ (Matrix.of X)
    with hD
  have hDi : Integrable D := (hT1 a (k + 1) γ (tail_max hord hgap)).const_mul _
  have hn1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hbound : ∀ (n : ℕ) (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ (k + 1))
      (X : Fin (k + 1) → Fin a → ℂ), ‖Φ u h ((n : ℝ) + 1) κ₁ κ₂ X‖ ≤ D X :=
    fun n κ₁ κ₂ X => norm_Φ_le hχ htie hu hh hCu hCh (hn1 n) κ₁ κ₂ X
  -- the innermost limit
  have hX : ∀ (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ (k + 1)),
      Tendsto (fun n : ℕ => ∫ X, Φ u h ((n : ℝ) + 1) κ₁ κ₂ X) atTop
        (𝓝 (u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) *
          ∫ X : Fin (k + 1) → Fin a → ℂ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
            blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
              (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)))) := by
    intro κ₁ κ₂
    rw [← integral_const_mul]
    have hcX : ∀ n : ℕ, Continuous fun X : Fin (k + 1) → Fin a → ℂ =>
        Φ u h ((n : ℝ) + 1) κ₁ κ₂ X := fun n =>
      continuous_Φ hu.1.continuous hh.1.continuous _ continuous_const continuous_const
        continuous_id
    refine tendsto_integral_of_dominated_convergence D
      (fun n => (hcX n).aestronglyMeasurable)
      hDi (fun n => ae_of_all _ (hbound n κ₁ κ₂)) (ae_of_all _ fun X => ?_)
    have hs : Tendsto (fun n : ℕ => ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) • Matrix.of X) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun n : ℕ => ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto 0).comp h0
        simpa [Function.comp_def, one_div] using this
      simpa using h1.smul_const (Matrix.of X)
    have hcont : Continuous fun Y : Matrix (Fin (k + 1)) (Fin a) ℂ =>
        u (blockLowerGL (a := a) (k := k + 1) Y *
          blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) :=
      hu.1.continuous.comp (continuous_blockLowerGL.mul continuous_const)
    have h2 := (hcont.tendsto 0).comp hs
    simp only [Function.comp_def, blockLowerGL_zero, one_mul] at h2
    exact h2.mul_const _
  -- the middle limit
  have hK2 : ∀ κ₁ : unitaryCompact ℂ a,
      Tendsto (fun n : ℕ => ∫ κ₂ : unitaryCompact ℂ (k + 1),
        (∫ X, Φ u h ((n : ℝ) + 1) κ₁ κ₂ X) ∂unitaryHaar (k + 1)) atTop
        (𝓝 (∫ κ₂ : unitaryCompact ℂ (k + 1), u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) *
          (∫ X : Fin (k + 1) → Fin a → ℂ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
            blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
              (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))) ∂unitaryHaar (k + 1))) := by
    intro κ₁
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ X, D X) (fun n => ?_)
      (integrable_const _) (fun n => ae_of_all _ fun κ₂ => ?_) (ae_of_all _ fun κ₂ => hX κ₁ κ₂)
    · exact AEStronglyMeasurable.integral_prod_right'
        (f := fun q : unitaryCompact ℂ (k + 1) × (Fin (k + 1) → Fin a → ℂ) =>
          Φ u h ((n : ℝ) + 1) κ₁ q.1 q.2)
        (continuous_Φ hu.1.continuous hh.1.continuous _ continuous_const continuous_fst
          continuous_snd).aestronglyMeasurable
    · exact norm_integral_le_of_norm_le hDi (ae_of_all _ (hbound n κ₁ κ₂))
  -- the outer limit
  have hlim : Tendsto (fun n : ℕ => ∫ κ₁ : unitaryCompact ℂ a, (∫ κ₂ : unitaryCompact ℂ (k + 1),
      (∫ X, Φ u h ((n : ℝ) + 1) κ₁ κ₂ X) ∂unitaryHaar (k + 1)) ∂unitaryHaar a) atTop
      (𝓝 (∫ κ₁ : unitaryCompact ℂ a, (∫ κ₂ : unitaryCompact ℂ (k + 1),
        u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
          (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) *
          (∫ X : Fin (k + 1) → Fin a → ℂ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
            blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
              (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)))
        ∂unitaryHaar (k + 1)) ∂unitaryHaar a)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ X, D X) (fun n => ?_)
      (integrable_const _) (fun n => ae_of_all _ fun κ₁ => ?_) (ae_of_all _ hK2)
    · exact AEStronglyMeasurable.integral_prod_right'
        (f := fun p : unitaryCompact ℂ a × unitaryCompact ℂ (k + 1) =>
          ∫ X, Φ u h ((n : ℝ) + 1) p.1 p.2 X)
        (AEStronglyMeasurable.integral_prod_right'
          (f := fun p : (unitaryCompact ℂ a × unitaryCompact ℂ (k + 1)) ×
            (Fin (k + 1) → Fin a → ℂ) => Φ u h ((n : ℝ) + 1) p.1.1 p.1.2 p.2)
          (continuous_Φ hu.1.continuous hh.1.continuous _
            (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst)
            continuous_snd).aestronglyMeasurable)
    · have := norm_integral_le_of_norm_le_const (μ := unitaryHaar (k + 1)) (C := ∫ X, D X)
        (ae_of_all _ fun κ₂ => norm_integral_le_of_norm_le hDi (ae_of_all _ (hbound n κ₁ κ₂)))
      simpa using this
  have hzero : ∀ n : ℕ, ∫ κ₁ : unitaryCompact ℂ a, (∫ κ₂ : unitaryCompact ℂ (k + 1),
      (∫ X, Φ u h ((n : ℝ) + 1) κ₁ κ₂ X) ∂unitaryHaar (k + 1)) ∂unitaryHaar a = 0 :=
    fun n => integral_Φ_eq_zero hT3 hχ hu hh h0 (by linarith [hn1 n])
  simp only [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end Limit

end ComplexBlockLimit

open ComplexDuality ComplexBlockParabolic ComplexBlockChart in
/-- **The limit argument along `P_{a,k+1}` of `GL_{a+k+1}(ℂ)`** (assuming
`ComplexBlockChartIntegrableStatement` and `ComplexBlockParabolicIntegrationStatement`). Let
`χ_0, χ_1, …` be characters of `ℂˣ` with `χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1` and
`|χ_l| = 1` on the unit circle, such that `Re e_{l+1} ≤ Re e_l` for `l < a`,
`Re e_a < Re e_{a−1}` (if `a ≥ 1`) and `Re e_a = Re e_{a+1} = ⋯ = Re e_{a+k}`. Let `u` lie in the
smooth principal series of the inverse characters and `h` in that of `χ` on `GL_{a+k+1}(ℂ)`. If
`∫_{U(a+k+1)} u(κ g) h(κ) dκ = 0` for every `g`, then
`∫_{U(a)} ∫_{U(k+1)} u(diag(κ₁, κ₂)) (∫_{M_{(k+1)×a}(ℂ)} h(n̄(X) diag(κ₁, κ₂)) dX) dκ₂ dκ₁ = 0`,
where `n̄(X) = [[1, 0], [X, 1]]` and `dκ₁, dκ₂` are the Haar probability measures. -/
def ComplexBlockLimitStatement : Prop :=
  ComplexBlockChartIntegrableStatement → ComplexBlockParabolicIntegrationStatement →
  ∀ (a k : ℕ) (χ : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ),
    (∀ (l : ℕ) (z : ℂˣ), χ l z =
      χ l (ComplexGramFormula.phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l) →
    (∀ l : ℕ, χ l 1 = 1) →
    (∀ (l : ℕ) (z : ℂˣ), ‖χ l (ComplexGramFormula.phaseUnit z)‖ = 1) →
    (∀ l : ℕ, l < a → (e (l + 1)).re ≤ (e l).re) →
    (∀ l : ℕ, l + 1 = a → (e (l + 1)).re < (e l).re) →
    (∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re) →
    ∀ u ∈ principalSeries ℂ (a + (k + 1)) (fun l z => (χ l z)⁻¹),
    ∀ h ∈ principalSeries ℂ (a + (k + 1)) χ,
      (∀ g : Langlands.GeneralLinear (a + (k + 1)) ℂ,
        ∫ κ, u ((κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) * g) * h κ
          ∂unitaryHaar (a + (k + 1)) = 0) →
      ∫ κ₁ : unitaryCompact ℂ a, (∫ κ₂ : unitaryCompact ℂ (k + 1),
        u (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) *
          (∫ X : Fin (k + 1) → Fin a → ℂ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
            blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)))
        ∂unitaryHaar (k + 1)) ∂unitaryHaar a = 0

theorem complexBlockLimit : ComplexBlockLimitStatement := by
  intro hT1 hT3 a k χ e heq hone hphase hord hgap htie u hu h hh h0
  have hχ : ComplexPartialJacquet.IsPhasePower χ e := ⟨heq, hone, hphase⟩
  exact ComplexBlockLimit.integral_mul_blockStep_eq_zero hT1 hT3 hχ htie hord hgap hu hh h0

end Langlands.Archimedean
