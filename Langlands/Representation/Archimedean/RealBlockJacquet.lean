import Langlands.Representation.Archimedean.RealBlockLimit

/-!
# The partial Jacquet integral along the maximal parabolic subgroup `P_{a,k+1}` of `GL_{a+k+1}(ℝ)`

For `h` in the principal series of signed-power characters `χ` of `GL_{a+k+1}(ℝ)` whose last
`k+1` exponents are tied (and strictly below the earlier ones), `T_P h(g) = ∫_X h(n̄(X) g) dX`
(`RealBlockJacquet.blockStep`), and for a continuous `φ` on `GL_{k+1}(ℝ)` the function
`h'(g₁) = ∫_{O(k+1)} φ(κ₂) T_P h(diag(g₁, κ₂)) dκ₂` (`RealBlockJacquet.blockPair`) is an
`O(a)`-finite function of the principal series of `GL_a(ℝ)` of the characters
`χ_l(x) |x|^{-(k+1)/2}`, assuming `RealBlockChartIntegrableStatement`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealBlockJacquet

open RealBlockParabolic RealBlockChart RealBlockLimit PartialJacquet JacquetLimit GramFormula
  PrincipalSeriesExtension RealPrincipalSeriesDuality Langlands.GeneralLinear

/-! ## Right multiplication of `M_{(k+1)×a}(ℝ)` by an invertible matrix -/

section RowMul

variable {a k : ℕ}

theorem det_vecMulLinearEquiv {B : Matrix (Fin a) (Fin a) ℝ} (hB : B.det ≠ 0) :
    LinearMap.det ((vecMulLinearEquiv hB : (Fin a → ℝ) ≃ₗ[ℝ] (Fin a → ℝ)) :
      (Fin a → ℝ) →ₗ[ℝ] (Fin a → ℝ)) = B.det := by
  have : ((vecMulLinearEquiv hB : (Fin a → ℝ) ≃ₗ[ℝ] (Fin a → ℝ)) :
      (Fin a → ℝ) →ₗ[ℝ] (Fin a → ℝ)) = Matrix.toLin' Bᵀ := by
    apply LinearMap.ext
    intro x
    simp [vecMulLinearEquiv, Matrix.toLin'_apply, mulVec_transpose]
  rw [this, LinearMap.det_toLin', det_transpose]

/-- `X ↦ X B` on `M_{(k+1)×a}(ℝ) = Fin (k+1) → Fin a → ℝ`, row by row. -/
def rowMulLinearEquiv {B : Matrix (Fin a) (Fin a) ℝ} (hB : B.det ≠ 0) :
    (Fin (k + 1) → Fin a → ℝ) ≃ₗ[ℝ] (Fin (k + 1) → Fin a → ℝ) :=
  LinearEquiv.piCongrRight fun _ => vecMulLinearEquiv hB

theorem det_rowMulLinearEquiv {B : Matrix (Fin a) (Fin a) ℝ} (hB : B.det ≠ 0) :
    LinearMap.det ((rowMulLinearEquiv (k := k) hB : (Fin (k + 1) → Fin a → ℝ) ≃ₗ[ℝ] _) :
      (Fin (k + 1) → Fin a → ℝ) →ₗ[ℝ] (Fin (k + 1) → Fin a → ℝ)) = B.det ^ (k + 1) := by
  have h : ((rowMulLinearEquiv (k := k) hB : (Fin (k + 1) → Fin a → ℝ) ≃ₗ[ℝ] _) :
      (Fin (k + 1) → Fin a → ℝ) →ₗ[ℝ] (Fin (k + 1) → Fin a → ℝ)) =
      LinearMap.pi (fun i : Fin (k + 1) =>
        ((vecMulLinearEquiv hB : (Fin a → ℝ) ≃ₗ[ℝ] (Fin a → ℝ)) :
          (Fin a → ℝ) →ₗ[ℝ] (Fin a → ℝ)).comp (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro X
    rfl
  rw [h, LinearMap.det_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    det_vecMulLinearEquiv]

/-- `X ↦ X B` as a measurable equivalence. -/
def rowMulEquiv {B : Matrix (Fin a) (Fin a) ℝ} (hB : B.det ≠ 0) :
    (Fin (k + 1) → Fin a → ℝ) ≃ᵐ (Fin (k + 1) → Fin a → ℝ) :=
  (LinearEquiv.toContinuousLinearEquiv
    (rowMulLinearEquiv (k := k) hB)).toHomeomorph.toMeasurableEquiv

theorem rowMulEquiv_apply {B : Matrix (Fin a) (Fin a) ℝ} (hB : B.det ≠ 0)
    (X : Fin (k + 1) → Fin a → ℝ) : rowMulEquiv hB X = fun i => X i ᵥ* B := rfl

/-- Lebesgue measure on `M_{(k+1)×a}(ℝ)` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_rows :
    (volume : Measure (Fin (k + 1) → Fin a → ℝ)).IsAddHaarMeasure := by
  rw [volume_pi]
  exact Measure.pi.isAddHaarMeasure _

/-- Lebesgue measure on `M_{(k+1)×a}(ℝ)` transforms under `X ↦ X B` by `|det B|^{-(k+1)}`. -/
theorem map_rowMulEquiv {B : Matrix (Fin a) (Fin a) ℝ} (hB : B.det ≠ 0) :
    Measure.map (rowMulEquiv (k := k) hB) volume =
      ENNReal.ofReal |(B.det ^ (k + 1))⁻¹| •
        (volume : Measure (Fin (k + 1) → Fin a → ℝ)) := by
  have hdet := det_rowMulLinearEquiv (k := k) hB
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin (k + 1) → Fin a → ℝ)))
    (f := ((rowMulLinearEquiv (k := k) hB : (Fin (k + 1) → Fin a → ℝ) ≃ₗ[ℝ] _) :
      (Fin (k + 1) → Fin a → ℝ) →ₗ[ℝ] (Fin (k + 1) → Fin a → ℝ)))
    (by rw [hdet]; exact pow_ne_zero _ hB)
  rw [hdet] at this
  exact this

theorem integral_rowMul_eq {B : Matrix (Fin a) (Fin a) ℝ} (hB : B.det ≠ 0)
    (f : (Fin (k + 1) → Fin a → ℝ) → ℂ) :
    ∫ X : Fin (k + 1) → Fin a → ℝ, f (fun i => X i ᵥ* B) =
      (((|B.det| ^ (k + 1))⁻¹ : ℝ) : ℂ) * ∫ X, f X := by
  have h := integral_map_equiv (μ := (volume : Measure (Fin (k + 1) → Fin a → ℝ)))
    (rowMulEquiv (k := k) hB) f
  rw [map_rowMulEquiv, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at h
  rw [show (∫ X : Fin (k + 1) → Fin a → ℝ, f (fun i => X i ᵥ* B)) =
      ∫ X, f (rowMulEquiv hB X) from rfl, ← h, Complex.real_smul, abs_inv, abs_pow]

end RowMul

/-! ## Block-diagonal and block-lower matrices -/

section Group

variable {a k : ℕ}

theorem blockDiagGL_mul (g₁ g₁' : Langlands.GeneralLinear a ℝ)
    (g₂ g₂' : Langlands.GeneralLinear k ℝ) :
    blockDiagGL (g₁ * g₁') (g₂ * g₂') = blockDiagGL g₁ g₂ * blockDiagGL g₁' g₂' := by
  apply Units.ext
  rw [Units.val_mul, blockDiagGL_val, blockDiagGL_val, blockDiagGL_val, Units.val_mul,
    Units.val_mul, RealBlockParabolic.blockDiag, RealBlockParabolic.blockDiag,
    RealBlockParabolic.blockDiag, reindex_mul_reindex, Matrix.fromBlocks_multiply]
  simp

theorem blockDiagGL_diagonalUnits (z : Fin a → ℝˣ) :
    blockDiagGL (Iwasawa.diagonalUnits z) (1 : Langlands.GeneralLinear k ℝ) =
      Iwasawa.diagonalUnits (Fin.addCases z (fun _ => 1)) := by
  apply Units.ext
  rw [blockDiagGL_val, Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val, Units.val_one,
    RealBlockParabolic.blockDiag]
  ext i j
  refine Fin.addCases (fun p => ?_) (fun q => ?_) i <;>
    refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, Fin.castAdd_inj, Fin.natAdd_inj]
  all_goals
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega

theorem blockDiagGL_mem_upperUnipotent (u : upperUnipotent a ℝ) :
    blockDiagGL (u : Langlands.GeneralLinear a ℝ) (1 : Langlands.GeneralLinear k ℝ) ∈
      upperUnipotent (a + k) ℝ := by
  have hval := blockDiagGL_val (u : Langlands.GeneralLinear a ℝ) (1 : Langlands.GeneralLinear k ℝ)
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    change j < i at hij
    change ((blockDiagGL (u : Langlands.GeneralLinear a ℝ) (1 : Langlands.GeneralLinear k ℝ) :
      Langlands.GeneralLinear (a + k) ℝ) : Matrix (Fin (a + k)) (Fin (a + k)) ℝ) i j = 0
    rw [hval, RealBlockParabolic.blockDiag]
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
  · change ((blockDiagGL (u : Langlands.GeneralLinear a ℝ) (1 : Langlands.GeneralLinear k ℝ) :
      Langlands.GeneralLinear (a + k) ℝ) : Matrix (Fin (a + k)) (Fin (a + k)) ℝ) i i = 1
    rw [hval, RealBlockParabolic.blockDiag]
    refine Fin.addCases (fun p => ?_) (fun q => ?_) i
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
        Matrix.fromBlocks_apply₁₁]
      exact u.2.2 p
    · simp

theorem blockLower_mul_blockDiag_one (X : Matrix (Fin k) (Fin a) ℝ)
    (B : Matrix (Fin a) (Fin a) ℝ) :
    blockLower X * RealBlockParabolic.blockDiag B 1 =
      RealBlockParabolic.blockDiag B 1 * blockLower (X * B) := by
  rw [blockLower, blockLower, RealBlockParabolic.blockDiag, reindex_mul_reindex,
    reindex_mul_reindex, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem blockLowerGL_mul_blockDiagGL (X : Matrix (Fin k) (Fin a) ℝ)
    (g : Langlands.GeneralLinear a ℝ) :
    blockLowerGL X * blockDiagGL g (1 : Langlands.GeneralLinear k ℝ) =
      blockDiagGL g 1 * blockLowerGL (X * (g : Matrix (Fin a) (Fin a) ℝ)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, RealBlockChart.blockLowerGL_val,
    RealBlockChart.blockLowerGL_val, blockDiagGL_val, Units.val_one]
  exact blockLower_mul_blockDiag_one X _

end Group

/-! ## The shifted characters -/

section Shift

variable {a k : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-- The shifted characters `χ_l(x) |x|^{-(k+1)/2}` of `GL_a(ℝ)`. -/
def blockShiftChar (k : ℕ) (χ : ℕ → ℝˣ → ℂ) (l : ℕ) (x : ℝˣ) : ℂ :=
  χ l x * ((|(x : ℝ)| : ℝ) : ℂ) ^ (-(((k : ℂ) + 1) / 2))

theorem isSignedPower_blockShift (hχ : IsSignedPower χ e) :
    IsSignedPower (blockShiftChar k χ) (fun l => e l - ((k : ℂ) + 1) / 2) where
  eq l x := by
    have hx : ((|(x : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr x.ne_zero
    rw [blockShiftChar, blockShiftChar, hχ.eq l x, abs_signUnit, Complex.ofReal_one,
      Complex.one_cpow, mul_one, mul_assoc, ← Complex.cpow_add _ _ hx]
    congr 2
  one l := by simp [blockShiftChar, hχ.one]
  norm_neg_one l := by simp [blockShiftChar, hχ.norm_neg_one]

theorem cpow_combine {x : ℂ} (hx : x ≠ 0) (c s₁ s₂ t : ℂ) (n : ℕ) (h : s₁ - n = t + s₂) :
    c * x ^ s₁ * (x ^ n)⁻¹ = c * x ^ t * x ^ s₂ := by
  rw [← Complex.cpow_natCast, ← Complex.cpow_neg, mul_assoc, mul_assoc,
    ← Complex.cpow_add _ _ hx, ← Complex.cpow_add _ _ hx, ← sub_eq_add_neg, h]

theorem principalSeriesCharacter_addCases (hχ1 : ∀ j : ℕ, a ≤ j → χ j 1 = 1)
    (z : Fin a → ℝˣ) :
    principalSeriesCharacter ℝ (a + (k + 1)) χ (Fin.addCases z (fun _ => 1)) *
        ((((∏ i, |(z i : ℝ)|) ^ (k + 1))⁻¹ : ℝ) : ℂ) =
      principalSeriesCharacter ℝ a (blockShiftChar k χ) z := by
  rw [principalSeriesCharacter, principalSeriesCharacter, Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd,
    Units.val_one, norm_one, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]
  rw [Finset.prod_eq_one (fun j _ => hχ1 _ (by omega)), mul_one]
  rw [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_prod, ← Finset.prod_pow,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [blockShiftChar]
  simp only [Module.finrank_self, pow_one, Real.norm_eq_abs]
  have hx : ((|(z i : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr (z i).ne_zero
  refine cpow_combine hx _ _ _ _ _ ?_
  push_cast
  ring

end Shift

/-! ## The partial Jacquet integral -/

section Step

variable {a k : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-- `T_P h(g) = ∫_{M_{(k+1)×a}(ℝ)} h(n̄(X) g) dX`. -/
def blockStep (h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ)
    (g : Langlands.GeneralLinear (a + (k + 1)) ℝ) : ℂ :=
  ∫ X : Fin (k + 1) → Fin a → ℝ, h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * g)

theorem of_mul_eq_of_vecMul (X : Fin (k + 1) → Fin a → ℝ) (B : Matrix (Fin a) (Fin a) ℝ) :
    Matrix.of X * B = Matrix.of (fun i => X i ᵥ* B) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

/-- **Equivariance.** `T_P h(diag(b g₁, g₂)) = χ'(b) T_P h(diag(g₁, g₂))` for `b = diag(z) u` in
the Borel subgroup of `GL_a(ℝ)`, with the shifted characters `χ' = blockShiftChar k χ`. -/
theorem blockStep_mul {h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hh : h ∈ principalSeries ℝ (a + (k + 1)) χ) (hχ1 : ∀ j : ℕ, a ≤ j → χ j 1 = 1)
    (z : Fin a → ℝˣ) (u : upperUnipotent a ℝ) (g₁ : Langlands.GeneralLinear a ℝ)
    (g₂ : Langlands.GeneralLinear (k + 1) ℝ) :
    blockStep h (blockDiagGL ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear a ℝ) *
        (u : Langlands.GeneralLinear a ℝ) * g₁) g₂) =
      principalSeriesCharacter ℝ a (blockShiftChar k χ) z * blockStep h (blockDiagGL g₁ g₂) := by
  set b : Langlands.GeneralLinear a ℝ :=
    (Iwasawa.diagonalUnits z : Langlands.GeneralLinear a ℝ) * (u : Langlands.GeneralLinear a ℝ)
    with hbdef
  have hdet : ((b : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ).det =
      ∏ i, (z i : ℝ) := by
    rw [hbdef, Units.val_mul, Matrix.det_mul, MaximalParabolicIntegration.det_upperUnipotent u,
      mul_one, Iwasawa.diagonalUnits_val, Matrix.det_diagonal]
  have hdet0 : ((b : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ).det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (z i).ne_zero
  have hsplit : blockDiagGL (b * g₁) g₂ =
      blockDiagGL b (1 : Langlands.GeneralLinear (k + 1) ℝ) * blockDiagGL g₁ g₂ := by
    rw [← blockDiagGL_mul, one_mul]
  have hb : blockDiagGL b (1 : Langlands.GeneralLinear (k + 1) ℝ) =
      (Iwasawa.diagonalUnits (Fin.addCases z (fun _ => 1)) :
        Langlands.GeneralLinear (a + (k + 1)) ℝ) *
      ((⟨blockDiagGL (u : Langlands.GeneralLinear a ℝ) (1 : Langlands.GeneralLinear (k + 1) ℝ),
        blockDiagGL_mem_upperUnipotent u⟩ : upperUnipotent (a + (k + 1)) ℝ) :
          Langlands.GeneralLinear (a + (k + 1)) ℝ) := by
    rw [← blockDiagGL_diagonalUnits]
    change blockDiagGL b 1 = blockDiagGL (Iwasawa.diagonalUnits z) 1 *
      blockDiagGL (u : Langlands.GeneralLinear a ℝ) 1
    rw [← blockDiagGL_mul, one_mul]
  have hpt : ∀ X : Fin (k + 1) → Fin a → ℝ,
      h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL (b * g₁) g₂) =
        principalSeriesCharacter ℝ (a + (k + 1)) χ (Fin.addCases z (fun _ => 1)) *
          h (blockLowerGL (a := a) (k := k + 1)
            (Matrix.of (fun i => X i ᵥ* ((b : Langlands.GeneralLinear a ℝ) :
              Matrix (Fin a) (Fin a) ℝ))) * blockDiagGL g₁ g₂) := by
    intro X
    rw [hsplit, ← mul_assoc, blockLowerGL_mul_blockDiagGL, mul_assoc, of_mul_eq_of_vecMul, hb]
    exact hh.2 _ _ _
  unfold blockStep
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul,
    integral_rowMul_eq hdet0 (fun Y => h (blockLowerGL (a := a) (k := k + 1) (Matrix.of Y) *
      blockDiagGL g₁ g₂)), ← mul_assoc, hdet, Finset.abs_prod,
    principalSeriesCharacter_addCases hχ1]

end Step

/-! ## Integrability, continuity and the paired function on `GL_a(ℝ)` -/

section Pair

open scoped Manifold ContDiff Matrix.Norms.Operator

attribute [local instance] measurableSpaceK secondCountableTopology_unitaryCompact

local instance borelSpaceK_bj (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {a k : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-- The order hypotheses of the block step: `Re e_a = ⋯ = Re e_{a+k}`, `Re e_{l+1} ≤ Re e_l` for
`l < a`, and `Re e_a < Re e_{a−1}`. -/
structure IsBlockDominant (e : ℕ → ℂ) (a k : ℕ) : Prop where
  tie : ∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re
  ord : ∀ l : ℕ, l < a → (e (l + 1)).re ≤ (e l).re
  gap : ∀ l : ℕ, l + 1 = a → (e (l + 1)).re < (e l).re

/-- The tail condition for the exponents `(Re e_{l+1} − Re e_l − 1)/2` of the block chart
bound. -/
theorem tail_h (he : IsBlockDominant e a k) :
    ∀ j : Fin a, ∑ l : Fin a, (if j ≤ l then
      ((e ((l : ℕ) + 1)).re - (e l).re - 1) / 2 + 1 / 2 else 0) < 0 := by
  intro j
  have hlast : (a - 1) < a := by have := j.isLt; omega
  set L : Fin a := ⟨a - 1, hlast⟩ with hL
  have hjL : j ≤ L := by
    rw [Fin.le_def]
    simp only [hL]
    have := j.isLt
    omega
  refine lt_of_lt_of_eq (Finset.sum_lt_sum (g := fun _ : Fin a => (0 : ℝ)) (fun l _ => ?_)
    ⟨L, Finset.mem_univ _, ?_⟩) Finset.sum_const_zero
  · split_ifs
    · have := he.ord l l.isLt
      linarith
    · exact le_refl _
  · rw [ite_eq_left hjL]
    have := he.gap (a - 1) (by omega)
    simp only [hL]
    linarith

theorem integrable_block (hT1 : RealBlockChartIntegrableStatement) (hχ : IsSignedPower χ e)
    (he : IsBlockDominant e a k) {h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hh : h ∈ principalSeries ℝ (a + (k + 1)) χ) {κ : Langlands.GeneralLinear (a + (k + 1)) ℝ}
    (hκ : κ ∈ unitaryCompact ℝ (a + (k + 1))) :
    Integrable fun X : Fin (k + 1) → Fin a → ℝ =>
      h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * κ) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hh.1.continuous
  refine Integrable.mono' ((hT1 a (k + 1) _ (tail_h he)).const_mul C) ?_
    (ae_of_all _ fun X => norm_le_block hχ he.tie hh hC (Matrix.of X) hκ)
  exact (hh.1.continuous.comp (continuous_blockLowerGL.mul continuous_const)).aestronglyMeasurable

theorem continuous_blockStep (hT1 : RealBlockChartIntegrableStatement) (hχ : IsSignedPower χ e)
    (he : IsBlockDominant e a k) {h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hh : h ∈ principalSeries ℝ (a + (k + 1)) χ) {T : Type*} [TopologicalSpace T]
    [FirstCountableTopology T] {f₁ : T → Langlands.GeneralLinear a ℝ}
    {f₂ : T → Langlands.GeneralLinear (k + 1) ℝ}
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (hm₁ : ∀ t, f₁ t ∈ unitaryCompact ℝ a)
    (hm₂ : ∀ t, f₂ t ∈ unitaryCompact ℝ (k + 1)) :
    Continuous fun t => blockStep h (blockDiagGL (f₁ t) (f₂ t)) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hh.1.continuous
  refine continuous_of_dominated
    (bound := fun X : Fin (k + 1) → Fin a → ℝ => C * blockChartBound
      (fun l : Fin a => ((e ((l : ℕ) + 1)).re - (e l).re - 1) / 2) (Matrix.of X))
    (fun t => ?_) (fun t => ae_of_all _ fun X => ?_) ((hT1 a (k + 1) _ (tail_h he)).const_mul C)
    (ae_of_all _ fun X => ?_)
  · exact (hh.1.continuous.comp (continuous_blockLowerGL.mul continuous_const)).aestronglyMeasurable
  · exact norm_le_block hχ he.tie hh hC _ (blockDiagGL_mem_unitaryCompact (hm₁ t) (hm₂ t))
  · exact hh.1.continuous.comp (continuous_const.mul
      (continuous_blockDiagGL.comp (hf₁.prodMk hf₂)))

theorem norm_blockStep_le (hT1 : RealBlockChartIntegrableStatement) (hχ : IsSignedPower χ e)
    (he : IsBlockDominant e a k) {h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hh : h ∈ principalSeries ℝ (a + (k + 1)) χ) {C : ℝ}
    (hC : ∀ κ ∈ unitaryCompact ℝ (a + (k + 1)), ‖h κ‖ ≤ C)
    {κ : Langlands.GeneralLinear (a + (k + 1)) ℝ} (hκ : κ ∈ unitaryCompact ℝ (a + (k + 1))) :
    ‖blockStep h κ‖ ≤ ∫ X : Fin (k + 1) → Fin a → ℝ, C * blockChartBound
      (fun l : Fin a => ((e ((l : ℕ) + 1)).re - (e l).re - 1) / 2) (Matrix.of X) :=
  norm_integral_le_of_norm_le ((hT1 a (k + 1) _ (tail_h he)).const_mul C)
    (ae_of_all _ fun X => norm_le_block hχ he.tie hh hC (Matrix.of X) hκ)

/-- `h'(g₁) = ∫_{O(k+1)} φ(κ₂) T_P h(diag(g₁, κ₂)) dκ₂`. -/
def blockPair (φ : Langlands.GeneralLinear (k + 1) ℝ → ℂ)
    (h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ) (g₁ : Langlands.GeneralLinear a ℝ) : ℂ :=
  ∫ κ₂ : unitaryCompact ℝ (k + 1),
    φ κ₂ * blockStep h (blockDiagGL g₁ (κ₂ : Langlands.GeneralLinear (k + 1) ℝ))
    ∂haarK (k + 1)

theorem blockPair_mul {φ : Langlands.GeneralLinear (k + 1) ℝ → ℂ}
    {h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hh : h ∈ principalSeries ℝ (a + (k + 1)) χ) (hχ1 : ∀ j : ℕ, a ≤ j → χ j 1 = 1)
    (z : Fin a → ℝˣ) (u : upperUnipotent a ℝ) (g₁ : Langlands.GeneralLinear a ℝ) :
    blockPair φ h ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear a ℝ) *
        (u : Langlands.GeneralLinear a ℝ) * g₁) =
      principalSeriesCharacter ℝ a (blockShiftChar k χ) z * blockPair φ h g₁ := by
  unfold blockPair
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun κ₂ => ?_)
  simp only
  rw [blockStep_mul hh hχ1]
  ring

theorem continuous_blockPair (hT1 : RealBlockChartIntegrableStatement) (hχ : IsSignedPower χ e)
    (he : IsBlockDominant e a k) {h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hh : h ∈ principalSeries ℝ (a + (k + 1)) χ) {φ : Langlands.GeneralLinear (k + 1) ℝ → ℂ}
    (hφ : Continuous φ) :
    Continuous fun κ : Matrix.unitaryGroup (Fin a) ℝ => blockPair φ h (Unitary.toUnits κ) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hh.1.continuous
  obtain ⟨Cφ, hCφ⟩ := exists_bound_unitaryCompact hφ
  have hCφ0 : 0 ≤ Cφ := le_trans (norm_nonneg _) (hCφ 1 (unitaryCompact ℝ _).one_mem)
  refine continuous_of_dominated (bound := fun _ => Cφ * ∫ X : Fin (k + 1) → Fin a → ℝ,
      C * blockChartBound (fun l : Fin a => ((e ((l : ℕ) + 1)).re - (e l).re - 1) / 2)
        (Matrix.of X))
    (fun κ => ?_) (fun κ => ae_of_all _ fun κ₂ => ?_) (integrable_const _)
    (ae_of_all _ fun κ₂ => ?_)
  · exact ((hφ.comp continuous_subtype_val).mul (continuous_blockStep hT1 hχ he hh
      (f₁ := fun _ => Unitary.toUnits κ) continuous_const continuous_subtype_val (fun _ => κ.2)
      (fun t => t.2))).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul (hCφ (κ₂ : Langlands.GeneralLinear (k + 1) ℝ) κ₂.2)
      (norm_blockStep_le hT1 hχ he hh hC (blockDiagGL_mem_unitaryCompact κ.2 κ₂.2))
      (norm_nonneg _) hCφ0
  · exact continuous_const.mul (continuous_blockStep hT1 hχ he hh
      (f₁ := fun κ : Matrix.unitaryGroup (Fin a) ℝ => Unitary.toUnits κ)
      (f₂ := fun _ => (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) continuous_unitary_toUnits
      continuous_const (fun κ => κ.2) (fun _ => κ₂.2))

/-- `h ↦ h'` restricted to `O(a)`, as a linear map on a submodule of the principal series. -/
def blockPairOn (hT1 : RealBlockChartIntegrableStatement) (hχ : IsSignedPower χ e)
    (he : IsBlockDominant e a k) {φ : Langlands.GeneralLinear (k + 1) ℝ → ℂ} (hφ : Continuous φ)
    (V : Submodule ℂ (Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ))
    (hV : V ≤ principalSeries ℝ (a + (k + 1)) χ) :
    V →ₗ[ℂ] (Matrix.unitaryGroup (Fin a) ℝ → ℂ) where
  toFun f κ := blockPair φ (f : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ) (Unitary.toUnits κ)
  map_add' f g := funext fun κ => by
    have hint : ∀ (f : V) (κ₂ : unitaryCompact ℝ (k + 1)), Integrable fun X : Fin (k + 1) →
        Fin a → ℝ => (f : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ)
          (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) *
            blockDiagGL (Unitary.toUnits κ) (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) :=
      fun f κ₂ => integrable_block hT1 hχ he (hV f.2) (blockDiagGL_mem_unitaryCompact κ.2 κ₂.2)
    have hcont : ∀ f : V, Integrable (fun κ₂ : unitaryCompact ℝ (k + 1) =>
        φ κ₂ * blockStep (f : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ)
          (blockDiagGL (Unitary.toUnits κ) (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)))
        (haarK (k + 1)) := fun f =>
      integrable_of_continuous ((hφ.comp continuous_subtype_val).mul
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

theorem blockPair_rightTranslation (φ : Langlands.GeneralLinear (k + 1) ℝ → ℂ)
    (f : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ) (g₁ κ : Langlands.GeneralLinear a ℝ) :
    blockPair φ (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℝ)
      (blockDiagGL κ (1 : Langlands.GeneralLinear (k + 1) ℝ)) f) g₁ = blockPair φ f (g₁ * κ) := by
  have hpt : ∀ (κ₂ : Langlands.GeneralLinear (k + 1) ℝ) (X : Fin (k + 1) → Fin a → ℝ),
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℝ)
        (blockDiagGL κ (1 : Langlands.GeneralLinear (k + 1) ℝ)) f
        (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL g₁ κ₂) =
      f (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL (g₁ * κ) κ₂) := by
    intro κ₂ X
    change f (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL g₁ κ₂ *
      blockDiagGL κ 1) = _
    rw [mul_assoc, ← blockDiagGL_mul, mul_one]
  simp only [blockPair, blockStep, hpt]

theorem finiteDimensional_blockPair (hT1 : RealBlockChartIntegrableStatement)
    (hχ : IsSignedPower χ e) (he : IsBlockDominant e a k)
    {h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hh : h ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) χ)
      (unitaryCompact ℝ (a + (k + 1))))
    {φ : Langlands.GeneralLinear (k + 1) ℝ → ℂ} (hφ : Continuous φ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun κ : Matrix.unitaryGroup (Fin a) ℝ =>
      fun x : Matrix.unitaryGroup (Fin a) ℝ => blockPair φ h (Unitary.toUnits (x * κ)))) := by
  set V := Submodule.span ℂ (Set.range fun κ : unitaryCompact ℝ (a + (k + 1)) =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℝ)
      (κ : Langlands.GeneralLinear (a + (k + 1)) ℝ) h) with hVdef
  have hVfin : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hh.2
  have hV : V ≤ principalSeries ℝ (a + (k + 1)) χ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨κ, rfl⟩
    exact rightTranslation_mem_principalSeries (χ := χ) hh.1 _
  have hle : Submodule.span ℂ (Set.range fun κ : Matrix.unitaryGroup (Fin a) ℝ =>
      fun x : Matrix.unitaryGroup (Fin a) ℝ => blockPair φ h (Unitary.toUnits (x * κ))) ≤
      LinearMap.range (blockPairOn hT1 hχ he hφ V hV) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨κ, rfl⟩
    have hκ : blockDiagGL (Unitary.toUnits κ) (1 : Langlands.GeneralLinear (k + 1) ℝ) ∈
        unitaryCompact ℝ (a + (k + 1)) :=
      blockDiagGL_mem_unitaryCompact κ.2 (unitaryCompact ℝ (k + 1)).one_mem
    refine ⟨⟨_, Submodule.subset_span ⟨⟨_, hκ⟩, rfl⟩⟩, funext fun x => ?_⟩
    change blockPair φ _ (Unitary.toUnits x) = blockPair φ h (Unitary.toUnits (x * κ))
    rw [blockPair_rightTranslation, map_mul]
  exact Submodule.finiteDimensional_of_le hle

/-- **The paired function.** `h'` is an `O(a)`-finite function of the principal series of the
shifted characters `blockShiftChar k χ` of `GL_a(ℝ)`. -/
theorem blockPair_mem (hT1 : RealBlockChartIntegrableStatement) (hχ : IsSignedPower χ e)
    (he : IsBlockDominant e a k) {h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hh : h ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) χ)
      (unitaryCompact ℝ (a + (k + 1))))
    {φ : Langlands.GeneralLinear (k + 1) ℝ → ℂ} (hφ : Continuous φ) :
    blockPair φ h ∈ kFiniteFunctions (principalSeries ℝ a (blockShiftChar k χ))
      (unitaryCompact ℝ a) := by
  have hχ1 : ∀ j : ℕ, a ≤ j → χ j 1 = 1 := fun j _ => hχ.one j
  set ψ : Matrix.unitaryGroup (Fin a) ℝ → ℂ := fun κ => blockPair φ h (Unitary.toUnits κ)
    with hψdef
  have hψc : Continuous ψ := continuous_blockPair hT1 hχ he hh.1 hφ
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun κ : Matrix.unitaryGroup (Fin a) ℝ => fun x => ψ (x * κ))) :=
    finiteDimensional_blockPair hT1 hχ he hh hφ
  have hψM : ∀ (d : Fin a → ℝˣ) (κ : Matrix.unitaryGroup (Fin a) ℝ),
      ψ (signDiagonal (fun i => (d i : ℝ)) * κ) =
        principalSeriesCharacter ℝ a (blockShiftChar k χ) (fun i => signUnit (d i)) * ψ κ := by
    intro d κ
    simp only [hψdef]
    rw [signDiagonal_toUnits, blockPair_mul hh.1 hχ1]
  have hE := extension_mem_kFiniteFunctions (fun l => e l - ((k : ℂ) + 1) / 2)
    (isSignedPower_blockShift hχ).eq hψc hfin hψM
  convert hE using 1
  funext g
  obtain ⟨z, u, κ, hκ, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  rw [blockPair_mul hh.1 hχ1, hE.1.2 z u κ]
  congr 1
  have hku : κ = Unitary.toUnits (⟨(κ : Matrix (Fin a) (Fin a) ℝ), hκ⟩ :
      Matrix.unitaryGroup (Fin a) ℝ) := Units.ext rfl
  rw [hku, extension_unitary]

end Pair

end RealBlockJacquet

open RealPrincipalSeriesDuality RealBlockParabolic RealBlockChart in
attribute [local instance] measurableSpaceK in
/-- **The partial Jacquet integral along `P_{a,k+1}` of `GL_{a+k+1}(ℝ)`** (assuming
`RealBlockChartIntegrableStatement`). Let `χ_0, χ_1, …` be characters of `ℝˣ` with
`χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and `‖χ_l(−1)‖ = 1`, such that
`Re e_{l+1} ≤ Re e_l` for `l < a`, `Re e_a < Re e_{a−1}` (if `a ≥ 1`) and
`Re e_a = ⋯ = Re e_{a+k}`. For every `O(a+k+1)`-finite function `h` of the smooth principal
series of `χ` on `GL_{a+k+1}(ℝ)`:
1. `X ↦ h(n̄(X) κ)` is integrable on `M_{(k+1)×a}(ℝ)` for every `κ ∈ O(a+k+1)`, where
   `n̄(X) = [[1, 0], [X, 1]]`;
2. for every continuous `φ` on `GL_{k+1}(ℝ)`, the function
   `g₁ ↦ ∫_{O(k+1)} φ(κ₂) (∫_X h(n̄(X) diag(g₁, κ₂)) dX) dκ₂` (`RealBlockJacquet.blockPair`) is an
   `O(a)`-finite function of the smooth principal series of `GL_a(ℝ)` of the characters
   `χ_l(x) |x|^{-(k+1)/2}` (`RealBlockJacquet.blockShiftChar k χ`). -/
def RealBlockJacquetStatement : Prop :=
  RealBlockChartIntegrableStatement →
  ∀ (a k : ℕ) (χ : ℕ → ℝˣ → ℂ) (e : ℕ → ℂ),
    (∀ (l : ℕ) (x : ℝˣ), χ l x = χ l (GramFormula.signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l) →
    (∀ l : ℕ, χ l 1 = 1) →
    (∀ l : ℕ, ‖χ l (-1)‖ = 1) →
    (∀ l : ℕ, l < a → (e (l + 1)).re ≤ (e l).re) →
    (∀ l : ℕ, l + 1 = a → (e (l + 1)).re < (e l).re) →
    (∀ j : ℕ, j ≤ k → (e (a + j)).re = (e a).re) →
    ∀ h ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) χ) (unitaryCompact ℝ (a + (k + 1))),
      (∀ κ ∈ unitaryCompact ℝ (a + (k + 1)), Integrable fun X : Fin (k + 1) → Fin a → ℝ =>
        h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * κ)) ∧
      ∀ φ : Langlands.GeneralLinear (k + 1) ℝ → ℂ, Continuous φ →
        RealBlockJacquet.blockPair φ h ∈
          kFiniteFunctions (principalSeries ℝ a (RealBlockJacquet.blockShiftChar k χ))
            (unitaryCompact ℝ a)

theorem realBlockJacquet : RealBlockJacquetStatement := by
  intro hT1 a k χ e heq hone hneg hord hgap htie h hh
  have hχ : PartialJacquet.IsSignedPower χ e := ⟨heq, hone, hneg⟩
  have he : RealBlockJacquet.IsBlockDominant e a k := ⟨htie, hord, hgap⟩
  exact ⟨fun κ hκ => RealBlockJacquet.integrable_block hT1 hχ he hh.1 hκ,
    fun φ hφ => RealBlockJacquet.blockPair_mem hT1 hχ he hh hφ⟩

end Langlands.Archimedean
