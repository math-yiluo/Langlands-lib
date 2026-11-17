import Langlands.Representation.Archimedean.RealLeviPairing

/-!
# Bump functions along a standard parabolic subgroup

For the standard parabolic subgroup `Q` of `GL_N(ℝ)` with diagonal blocks of sizes
`sz_0, …, sz_{c-1}` and first block positions `l_i`, the function
`ω(g) = ∏_i m_{l_i}(g)² / G_{l_i}(g)`, with `m_l(g)` the minor of `g` on the rows and columns
`≥ l` and `G_l(g)` the Gram determinant of the rows `≥ l`, is invariant under left
multiplication by upper triangular matrices and under left and right multiplication by the
block orthogonal group `∏_i O(sz_i)`. On `O(N)` it is a polynomial in the matrix entries.
Multiplying an `O(N)`-finite vector `f` of a principal series by `ω^m` therefore gives another
`O(N)`-finite vector of the same principal series (and of the same standard module). On the
opposite unipotent radical, `β(X) = ω(n̄(X)) = ∏_i G_{l_i}(n̄(X))⁻¹` is continuous, equals `1`
exactly at `X = 0`, and is bounded away from `1` outside every ball around `0`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviBump

open RealInducedBlockBound RealInducedTorusCore RealLeviChart GramFormula RealLeviTorus
  RealLeviLimit RealPrincipalSeriesDuality PartialJacquet RealInducedStandardBound
  RealStrictCharacterLanglandsQuotient RealLeviModes RealLeviPairing RealBlockFourierFinite
  PrincipalSeriesExtension

/-! ## Padded matrices and Gram determinants -/

section Pad

variable {n : ℕ}

theorem padded_mul (l : ℕ) {W Z : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ p q r : Fin n, l ≤ (p : ℕ) → l ≤ (q : ℕ) → (r : ℕ) < l → W p r * Z r q = 0) :
    padded l (W * Z) = padded l W * padded l Z := by
  ext p q
  by_cases hp : l ≤ (p : ℕ)
  · by_cases hq : l ≤ (q : ℕ)
    · have lhs : padded l (W * Z) p q = ∑ r, W p r * Z r q := by
        simp only [padded, Matrix.of_apply]
        rw [ite_eq_left ⟨hp, hq⟩, Matrix.mul_apply]
      rw [lhs, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : l ≤ (r : ℕ)
      · simp only [padded, Matrix.of_apply]
        rw [ite_eq_left ⟨hp, hr⟩, ite_eq_left ⟨hr, hq⟩]
      · rw [h p q r hp hq (by omega)]
        simp only [padded, Matrix.of_apply]
        rw [ite_eq_right (fun h' => hr h'.2), Matrix.one_apply_ne (fun e => by subst e; omega),
          zero_mul]
    · have hcol : ∀ r : Fin n, padded l Z r q = (1 : Matrix (Fin n) (Fin n) ℝ) r q := fun r => by
        simp only [padded, Matrix.of_apply]
        rw [ite_eq_right (fun h' => hq h'.2)]
      rw [Matrix.mul_apply]
      simp_rw [hcol]
      rw [← Matrix.mul_apply, Matrix.mul_one]
      simp only [padded, Matrix.of_apply]
      rw [ite_eq_right (fun h' => hq h'.2), ite_eq_right (fun h' => hq h'.2)]
  · rw [mul_apply_of_row_single (row_padded_of_lt W (by omega : (p : ℕ) < l))]
    simp only [padded, Matrix.of_apply]
    rw [ite_eq_right (fun h' => hp h'.1), ite_eq_right (fun h' => hp h'.1)]

theorem padded_one (l : ℕ) : padded l (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext p q
  simp only [padded, Matrix.of_apply]
  split_ifs <;> rfl

theorem padded_transpose (l : ℕ) (W : Matrix (Fin n) (Fin n) ℝ) :
    padded l Wᵀ = (padded l W)ᵀ := by
  ext p q
  simp only [padded, Matrix.of_apply, Matrix.transpose_apply]
  by_cases h : l ≤ (p : ℕ) ∧ l ≤ (q : ℕ)
  · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.2, h'.1⟩)]
    by_cases e : p = q
    · subst e
      rfl
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (Ne.symm e)]

theorem padded_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (l : ℕ)
    (b : Matrix (Fin n) (Fin n) R) : padded l (b.map φ) = (padded l b).map φ := by
  ext p q
  simp only [padded, Matrix.of_apply, Matrix.map_apply]
  split_ifs
  · rfl
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem gram_mul_left (l : ℕ) {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : ∀ p q : Fin n, l ≤ (p : ℕ) → (q : ℕ) < l → W p q = 0) (Z : Matrix (Fin n) (Fin n) ℝ) :
    GramFormula.gram l (W * Z) = (padded l W).det ^ 2 * GramFormula.gram l Z := by
  rw [GramFormula.gram, GramFormula.gram, paddedGram_mul_of_blockUpper l hW, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  ring

theorem gram_mul_orth (l : ℕ) (Z : Matrix (Fin n) (Fin n) ℝ) {k : Matrix (Fin n) (Fin n) ℝ}
    (hk : k * kᵀ = 1) : GramFormula.gram l (Z * k) = GramFormula.gram l Z := by
  have e : Z * k * (Z * k)ᵀ = Z * Zᵀ := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k, hk, Matrix.one_mul]
  simp only [GramFormula.gram, GramFormula.paddedGram, e]

theorem gram_of_orth (l : ℕ) {k : Matrix (Fin n) (Fin n) ℝ} (hk : k * kᵀ = 1) :
    GramFormula.gram l k = 1 := by
  have h1 := gram_mul_orth l (1 : Matrix (Fin n) (Fin n) ℝ) hk
  rw [Matrix.one_mul] at h1
  rw [h1, GramFormula.gram]
  have : GramFormula.paddedGram l (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    ext p q
    simp only [GramFormula.paddedGram, Matrix.of_apply, Matrix.transpose_one, Matrix.mul_one]
    split_ifs <;> rfl
  rw [this, Matrix.det_one]

theorem det_padded_sq (l : ℕ) {k : Matrix (Fin n) (Fin n) ℝ} (hk : k * kᵀ = 1)
    (hW : ∀ p q : Fin n, l ≤ (p : ℕ) → (q : ℕ) < l → k p q = 0) :
    (padded l k).det ^ 2 = 1 := by
  have h1 : padded l (k * kᵀ) = padded l k * padded l kᵀ :=
    padded_mul l fun p q r hp _ hr => by rw [hW p r hp hr, zero_mul]
  rw [hk, padded_one, padded_transpose] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_one, Matrix.det_mul, Matrix.det_transpose] at h2
  rw [sq, ← h2]

theorem det_padded_ne_zero (l : ℕ) {k : Matrix (Fin n) (Fin n) ℝ} (hk : k * kᵀ = 1)
    (hW : ∀ p q : Fin n, l ≤ (p : ℕ) → (q : ℕ) < l → k p q = 0) :
    (padded l k).det ≠ 0 := fun h => by
  have := det_padded_sq l hk hW
  rw [h] at this
  norm_num at this

/-- `m_l(Z)² / G_l(Z)`, where `m_l(Z)` is the minor of `Z` on the rows and columns `≥ l` and
`G_l(Z)` the Gram determinant of the rows `≥ l`. -/
def bumpFactor (l : ℕ) (Z : Matrix (Fin n) (Fin n) ℝ) : ℝ := (padded l Z).det ^ 2 / GramFormula.gram l Z

theorem bumpFactor_mul_left (l : ℕ) {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : ∀ p q : Fin n, l ≤ (p : ℕ) → (q : ℕ) < l → W p q = 0) (hd : (padded l W).det ≠ 0)
    (Z : Matrix (Fin n) (Fin n) ℝ) : bumpFactor l (W * Z) = bumpFactor l Z := by
  unfold bumpFactor
  rw [padded_mul l fun p q r hp _ hr => by rw [hW p r hp hr, zero_mul], Matrix.det_mul,
    gram_mul_left l hW, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

theorem bumpFactor_mul_right (l : ℕ) (Z : Matrix (Fin n) (Fin n) ℝ)
    {k : Matrix (Fin n) (Fin n) ℝ} (hk : k * kᵀ = 1)
    (hup : ∀ p q : Fin n, l ≤ (p : ℕ) → (q : ℕ) < l → k p q = 0)
    (hlow : ∀ p q : Fin n, (p : ℕ) < l → l ≤ (q : ℕ) → k p q = 0) :
    bumpFactor l (Z * k) = bumpFactor l Z := by
  unfold bumpFactor
  rw [padded_mul l fun p q r _ hq hr => by rw [hlow r q hr hq, mul_zero], Matrix.det_mul,
    mul_pow, det_padded_sq l hk hup, mul_one, gram_mul_orth l Z hk]

theorem bumpFactor_of_orth (l : ℕ) {k : Matrix (Fin n) (Fin n) ℝ} (hk : k * kᵀ = 1) :
    bumpFactor l k = (padded l k).det ^ 2 := by
  rw [bumpFactor, gram_of_orth l hk, div_one]

theorem bumpFactor_of_lower (l : ℕ) {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hL1 : ∀ p, L p p = 1) : bumpFactor l L = (GramFormula.gram l L)⁻¹ := by
  rw [bumpFactor, det_padded_of_lower l hL hL1, one_pow, one_div]

/-- `det (1 + Y Yᵀ) > 1` for a nonzero real matrix `Y`. -/
theorem one_lt_det_one_add {m : Type*} [Fintype m] [DecidableEq m] {Y : Matrix m m ℝ}
    (hY : Y ≠ 0) : 1 < (1 + Y * Yᵀ).det := by
  have hA : (Y * Yᵀ).PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose Y
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have e := RealBlockLimit.det_one_add_smul_eq_prod hA 1
  rw [one_smul] at e
  rw [e]
  have htr : (Y * Yᵀ).trace = ∑ i, hA.1.eigenvalues i := by
    have := hA.1.trace_eq_sum_eigenvalues
    simpa using this
  have hpos : 0 < (Y * Yᵀ).trace := by
    obtain ⟨i, j, hij⟩ : ∃ i j, Y i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hY (Matrix.ext h)
    have e2 : (Y * Yᵀ).trace = ∑ i', ∑ j', Y i' j' * Y i' j' := by
      rw [Matrix.trace]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Matrix.diag_apply, Matrix.mul_apply]
      rfl
    rw [e2]
    refine lt_of_lt_of_le (mul_self_pos.mpr hij) ?_
    calc Y i j * Y i j ≤ ∑ j', Y i j' * Y i j' :=
          Finset.single_le_sum (f := fun j' => Y i j' * Y i j')
            (fun j' _ => mul_self_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', Y i' j' * Y i' j' :=
          Finset.single_le_sum (f := fun i' => ∑ j', Y i' j' * Y i' j')
            (fun i' _ => Finset.sum_nonneg fun j' _ => mul_self_nonneg _) (Finset.mem_univ i)
  rw [htr] at hpos
  obtain ⟨i0, -, hi0⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
    (f := fun _ => (0 : ℝ)) (g := fun i => hA.1.eigenvalues i) (by simpa using hpos)
  have hnn : ∀ i, 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg
  have h1 : (1 : ℝ) ≤ ∏ i ∈ Finset.univ.erase i0, (1 + 1 * hA.1.eigenvalues i) := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ.erase i0) (f := fun _ : m => (1 : ℝ))
      (g := fun i => 1 + 1 * hA.1.eigenvalues i) (fun _ _ => zero_le_one)
      (fun i _ => by have := hnn i; linarith)
    simpa using h
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
  calc (1 : ℝ) < 1 + 1 * hA.1.eigenvalues i0 := by linarith
    _ = (1 + 1 * hA.1.eigenvalues i0) * 1 := (mul_one _).symm
    _ ≤ (1 + 1 * hA.1.eigenvalues i0) *
        ∏ i ∈ Finset.univ.erase i0, (1 + 1 * hA.1.eigenvalues i) :=
          mul_le_mul_of_nonneg_left h1 (by have := hnn i0; linarith)

end Pad

/-! ## The function `ω` -/

section Levi

variable {c : ℕ} (sz : Fin c → ℕ)

theorem start_mono {i j : ℕ} (h : i ≤ j) : start sz i ≤ start sz j := by
  unfold start
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

theorem start_le_iff (i : Fin c) (p : Fin (∑ i, sz i)) :
    start sz (i : ℕ) ≤ (p : ℕ) ↔ i ≤ cls sz p := by
  obtain ⟨a, ha⟩ := pos_cls sz p
  have hp : (p : ℕ) = start sz (cls sz p) + a := by rw [← val_pos, ha]
  constructor
  · intro h
    by_contra hlt
    have hlt' : cls sz p < i := not_le.mp hlt
    have hs := start_succ_le sz (Fin.lt_def.mp hlt') (cls sz p).2
    have e : sz ⟨((cls sz p : Fin c) : ℕ), (cls sz p).2⟩ = sz (cls sz p) := rfl
    rw [e] at hs
    have := a.2
    omega
  · intro h
    have := start_mono sz (Fin.le_def.mp h)
    omega

theorem blockUpper_of_blockZero {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ}
    (hk : BlockZero sz k) (i : Fin c) :
    ∀ p q : Fin (∑ i, sz i), start sz (i : ℕ) ≤ (p : ℕ) → (q : ℕ) < start sz (i : ℕ) →
      k p q = 0 :=
  fun p q hp hq => hk p q fun e => (not_le.mpr hq) ((start_le_iff sz i q).mpr
    (by rw [← e]; exact (start_le_iff sz i p).mp hp))

theorem blockLower_of_blockZero {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ}
    (hk : BlockZero sz k) (i : Fin c) :
    ∀ p q : Fin (∑ i, sz i), (p : ℕ) < start sz (i : ℕ) → start sz (i : ℕ) ≤ (q : ℕ) →
      k p q = 0 :=
  fun p q hp hq => hk p q fun e => (not_le.mpr hp) ((start_le_iff sz i p).mpr
    (by rw [e]; exact (start_le_iff sz i q).mp hq))

/-- `ω(Z) = ∏_i m_{l_i}(Z)² / G_{l_i}(Z)` over the first positions `l_i` of the blocks. -/
def omega (Z : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) : ℝ :=
  ∏ i : Fin c, bumpFactor (start sz (i : ℕ)) Z

theorem omega_mul_upper {b : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ}
    (hb : b.IsUpperTriangular) (hd : ∀ l, b l l ≠ 0)
    (Z : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) : omega sz (b * Z) = omega sz Z :=
  Finset.prod_congr rfl fun _ _ => bumpFactor_mul_left _
    (fun p q hp hq => hb (show q < p by rw [Fin.lt_def]; omega))
    (by rw [det_padded hb]; exact diagonalTail_ne_zero hd _) Z

theorem omega_mul_left {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ} (hk : k * kᵀ = 1)
    (h0 : BlockZero sz k) (Z : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) :
    omega sz (k * Z) = omega sz Z :=
  Finset.prod_congr rfl fun i _ => bumpFactor_mul_left _ (blockUpper_of_blockZero sz h0 i)
    (det_padded_ne_zero _ hk (blockUpper_of_blockZero sz h0 i)) Z

theorem omega_mul_right (Z : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)
    {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ} (hk : k * kᵀ = 1) (h0 : BlockZero sz k) :
    omega sz (Z * k) = omega sz Z :=
  Finset.prod_congr rfl fun i _ => bumpFactor_mul_right _ Z hk
    (blockUpper_of_blockZero sz h0 i) (blockLower_of_blockZero sz h0 i)

theorem omega_of_orth {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ} (hk : k * kᵀ = 1) :
    omega sz k = ∏ i : Fin c, (padded (start sz (i : ℕ)) k).det ^ 2 :=
  Finset.prod_congr rfl fun _ _ => bumpFactor_of_orth _ hk

/-- `β(X) = ω(n̄(X))`. -/
def beta (X : Coord sz → ℝ) : ℝ := omega sz (RealLeviChart.lower sz X)

theorem beta_eq (X : Coord sz → ℝ) :
    beta sz X = ∏ i : Fin c, (GramFormula.gram (start sz (i : ℕ)) (RealLeviChart.lower sz X))⁻¹ := by
  unfold beta omega
  exact Finset.prod_congr rfl fun _ _ =>
    bumpFactor_of_lower _ (lower_isLowerTriangular sz X) (lower_apply_self sz X)

/-- The matrix of the coordinate functions. -/
def entryMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun p q => MvPolynomial.X (p, q)

/-- The polynomial `∏_i m_{l_i}²`, equal to `ω` on `O(N)`. -/
def omegaPoly : MvPolynomial (Fin (∑ i, sz i) × Fin (∑ i, sz i)) ℂ :=
  ∏ i : Fin c, (padded (start sz (i : ℕ)) (entryMatrix (∑ i, sz i))).det ^ 2

theorem eval_omegaPoly (k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) :
    MvPolynomial.eval (fun ij => ((k ij.1 ij.2 : ℝ) : ℂ)) (omegaPoly sz) =
      ((∏ i : Fin c, (padded (start sz (i : ℕ)) k).det ^ 2 : ℝ) : ℂ) := by
  have hm : (entryMatrix (∑ i, sz i)).map
      (MvPolynomial.eval fun ij => ((k ij.1 ij.2 : ℝ) : ℂ)) = k.map Complex.ofRealHom := by
    ext p q
    simp [entryMatrix]
  unfold omegaPoly
  rw [map_prod, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, Complex.ofReal_pow, RingHom.map_det, RingHom.mapMatrix_apply, ← padded_map, hm,
    padded_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

end Levi

/-! ## Multiplication by powers of `ω` -/

section Bump

variable {c : ℕ} (sz : Fin c → ℕ)

/-- **Bump.** For an `O(N)`-finite vector `f` of a principal series and `m : ℕ`, the function
`ω^m f` is an `O(N)`-finite vector of the same principal series. -/
theorem exists_bump {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (hχ : IsSignedPower χ e)
    {f : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i) χ) (unitaryCompact ℝ (∑ i, sz i)))
    (m : ℕ) :
    ∃ f' ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i) χ) (unitaryCompact ℝ (∑ i, sz i)),
      ∀ g : Langlands.GeneralLinear (∑ i, sz i) ℝ,
        f' g = ((omega sz (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) : ℝ) : ℂ) ^ m *
          f g := by
  have hfc : Continuous f := hf.1.1.continuous
  obtain ⟨P, hP⟩ := OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors hfc hf.2 1
  have horth : ∀ κ : Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ,
      (κ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) *
        (κ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)ᵀ = 1 := fun κ => by
    have := Matrix.mem_unitaryGroup_iff.mp κ.2
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  let Q : MvPolynomial (Fin (∑ i, sz i) × Fin (∑ i, sz i)) ℂ := omegaPoly sz ^ m * P
  let φ : Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ → ℂ := fun κ => MvPolynomial.eval
    (fun ij => (((κ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) ij.1 ij.2 : ℝ) : ℂ)) Q
  have hφval : ∀ κ, φ κ =
      ((omega sz (κ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) : ℝ) : ℂ) ^ m *
        f (Unitary.toUnits κ) := by
    intro κ
    show MvPolynomial.eval _ (omegaPoly sz ^ m * P) = _
    rw [map_mul, map_pow, eval_omegaPoly, ← hP κ, one_mul, omega_of_orth sz (horth κ)]
  have hφc : Continuous φ :=
    (MvPolynomial.continuous_eval Q).comp (continuous_pi fun ij => Complex.continuous_ofReal.comp
      ((continuous_apply ij.2).comp ((continuous_apply ij.1).comp continuous_subtype_val)))
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ => fun x => φ (x * k))) :=
    TranslateFinite.finiteDimensional_span_eval (n := ∑ i, sz i) Q
  have hφs : ∀ (i : Fin (∑ i, sz i)) (κ : Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ),
      φ (signReflection (∑ i, sz i) i * κ) = χ i (-1) * φ κ := by
    intro i κ
    have e : ((signReflection (∑ i, sz i) i * κ : Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ) :
        Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) =
        Matrix.diagonal (fun i' => if i' = i then (-1 : ℝ) else 1) *
          (κ : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) := rfl
    rw [hφval, hφval, e, omega_mul_upper sz (Matrix.blockTriangular_diagonal _)
      (fun l => by rw [Matrix.diagonal_apply_eq]; split_ifs <;> norm_num), map_mul,
      apply_signReflection_mul hχ.one hf.1 i]
    ring
  have hφM := apply_signDiagonal_mul hχ.one hφs
  have hE := extension_mem_kFiniteFunctions e hχ.eq hφc hfin hφM
  refine ⟨_, hE, fun g => ?_⟩
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  rw [hE.1.2 a u k, hf.1.2 a u k]
  have hku : k = Unitary.toUnits (⟨(k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ), hk⟩ :
      Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ) := Units.ext rfl
  have hω : omega sz (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear (∑ i, sz i) ℝ) *
      (u : Langlands.GeneralLinear (∑ i, sz i) ℝ) * k : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
        Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) =
      omega sz (k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) := by
    rw [Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val]
    exact omega_mul_upper sz (isUpperTriangular_diagonal_mul a u)
      (fun l => by rw [diagonal_mul_apply_self a u l]; exact (a l).ne_zero) _
  have hext : extension (shiftedExponent (∑ i, sz i) e) φ k =
      φ ⟨(k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ), hk⟩ := by
    calc extension (shiftedExponent (∑ i, sz i) e) φ k =
        extension (shiftedExponent (∑ i, sz i) e) φ (Unitary.toUnits
          (⟨(k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ), hk⟩ :
            Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ)) := congrArg _ hku
      _ = _ := extension_unitary _ _ _
  rw [hω, hext, hφval, ← hku]
  have : (((⟨(k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ), hk⟩ :
      Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ)) : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) =
        (k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) := rfl
  rw [this]
  ring

/-- **Bump in the standard module.** If the induction blocks of `ds` lie inside the blocks of
`Q`, multiplication by `ω^m` preserves the `O(N)`-finite vectors of the standard module. -/
theorem exists_bump_standard {ds : List RealBlock} (hN : realRank ds = ∑ i, sz i)
    (hstrict : ∀ p q : Fin (∑ i, sz i), cls sz p < cls sz q →
      realPositionBlockExponent ds q < realPositionBlockExponent ds p)
    {f : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
      (unitaryCompact ℝ (∑ i, sz i))) (m : ℕ) :
    ∃ f' ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds) (unitaryCompact ℝ (∑ i, sz i)),
      ∀ g : Langlands.GeneralLinear (∑ i, sz i) ℝ,
        f' g = ((omega sz (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) : ℝ) : ℂ) ^ m *
          f g := by
  obtain ⟨f', hf', hfg⟩ := exists_bump sz (isSignedPower ds) ⟨hf.1.1, hf.2⟩ m
  refine ⟨f', mem_kFin_standard_of_window hN hf' fun s hs j hj k _ => ?_, hfg⟩
  have hcls := slots_cls_eq hstrict s hs
  have hrot : ∀ θ : ℝ, omega sz ((blockRotation (∑ i, sz i) s.p θ * k :
      Langlands.GeneralLinear (∑ i, sz i) ℝ) : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) =
        omega sz (k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) := fun θ => by
    obtain ⟨h1, h2⟩ := mem_blockOrth_iff.mp (blockRotation_mem_blockOrth s.hp hcls θ)
    rw [Units.val_mul]
    exact omega_mul_left sz h1 h2 _
  have h0 := window_of_mem_standard hf.1 s hs j hj k
  unfold blockFourierCoefficient at h0 ⊢
  have e : (fun θ : ℝ => f' (blockRotation (∑ i, sz i) s.p θ * k) *
      Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))) = fun θ =>
        ((omega sz (k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) : ℝ) : ℂ) ^ m *
          (f (blockRotation (∑ i, sz i) s.p θ * k) *
            Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))) :=
    funext fun θ => by rw [hfg, hrot, mul_assoc]
  rw [e, intervalIntegral.integral_const_mul, h0, mul_zero]

end Bump

/-! ## The function `β` on the opposite unipotent radical -/

section Beta

variable {c : ℕ} {sz : Fin c → ℕ}

theorem continuous_beta : Continuous (beta sz) := by
  have e : beta sz = fun X => ∏ i : Fin c, (GramFormula.gram (start sz (i : ℕ)) (RealLeviChart.lower sz X))⁻¹ :=
    funext (beta_eq sz)
  rw [e]
  exact continuous_finsetProd _ fun i _ => (continuous_gram continuous_lower _).inv₀ fun X =>
    (zero_lt_one.trans_le (one_le_gram_lower sz X _)).ne'

theorem beta_pos (X : Coord sz → ℝ) : 0 < beta sz X := by
  rw [beta_eq]
  exact Finset.prod_pos fun i _ => inv_pos.mpr (zero_lt_one.trans_le (one_le_gram_lower sz X _))

theorem beta_le_one (X : Coord sz → ℝ) : beta sz X ≤ 1 := by
  rw [beta_eq]
  exact Finset.prod_le_one₀
    (fun i _ => (inv_pos.mpr (zero_lt_one.trans_le (one_le_gram_lower sz X _))).le)
    fun i _ => inv_le_one_of_one_le₀ (one_le_gram_lower sz X _)

theorem beta_zero : beta sz 0 = 1 := by
  rw [beta_eq]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [RealLeviLimit.lower_zero,
    gram_of_orth _ (by rw [Matrix.transpose_one, Matrix.mul_one]), inv_one]

theorem beta_le_beta_scale {s : ℝ} (hs : 1 ≤ s) (X : Coord sz → ℝ) :
    beta sz X ≤ beta sz (scaleCoord sz s X) := by
  rw [beta_eq, beta_eq]
  exact Finset.prod_le_prod₀
    (fun i _ => (inv_pos.mpr (zero_lt_one.trans_le (one_le_gram_lower sz X _))).le)
    fun i _ => inv_anti₀ (zero_lt_one.trans_le (one_le_gram_lower sz _ _))
      (gram_lower_scaleCoord_le sz hs X _)

theorem scaleCoord_one (X : Coord sz → ℝ) : scaleCoord sz 1 X = X := by
  funext pq
  simp [scaleCoord, scaleVec]

theorem norm_scaleCoord_le {s : ℝ} (hs : 1 ≤ s) (X : Coord sz → ℝ) :
    ‖scaleCoord sz s X‖ ≤ ‖X‖ / s := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  refine (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg _) hs0.le)).mpr fun pq => ?_
  have hlt : (cls sz pq.1.2 : ℕ) < (cls sz pq.1.1 : ℕ) := pq.2
  have hratio : scaleVec sz s pq.1.2 / scaleVec sz s pq.1.1 ≤ 1 / s := by
    unfold scaleVec
    obtain ⟨d, hd⟩ : ∃ d, (cls sz pq.1.1 : ℕ) = (cls sz pq.1.2 : ℕ) + (d + 1) :=
      ⟨(cls sz pq.1.1 : ℕ) - (cls sz pq.1.2 : ℕ) - 1, by omega⟩
    rw [hd, pow_add, div_mul_cancel_left₀ (pow_ne_zero _ hs0.ne'), one_div]
    exact inv_anti₀ hs0 (le_self_pow₀ hs (by omega))
  have hr0 : 0 ≤ scaleVec sz s pq.1.2 / scaleVec sz s pq.1.1 :=
    div_nonneg (scaleVec_pos sz hs0 _).le (scaleVec_pos sz hs0 _).le
  show ‖scaleVec sz s pq.1.2 / scaleVec sz s pq.1.1 * X pq‖ ≤ ‖X‖ / s
  rw [norm_mul, Real.norm_of_nonneg hr0, div_eq_mul_one_div ‖X‖ s, mul_comm ‖X‖]
  exact mul_le_mul hratio (norm_le_pi_norm X pq) (norm_nonneg _) (by positivity)

theorem continuousOn_scaleCoord (X : Coord sz → ℝ) :
    ContinuousOn (fun s : ℝ => scaleCoord sz s X) (Set.Ioi 0) := by
  refine continuousOn_pi.mpr fun pq => ?_
  unfold scaleCoord scaleVec
  exact ((continuousOn_pow _).div (continuousOn_pow _)
    fun s hs => pow_ne_zero _ (ne_of_gt hs)).mul continuousOn_const

/-- `β(Y) < 1` for `Y ≠ 0`. -/
theorem beta_lt_one {Y : Coord sz → ℝ} (hY : Y ≠ 0) : beta sz Y < 1 := by
  have hex : ∃ pq : Coord sz, Y pq ≠ 0 := by
    by_contra h
    push Not at h
    exact hY (funext h)
  let T : Finset (Coord sz) := Finset.univ.filter fun pq => Y pq ≠ 0
  have hT : T.Nonempty := let ⟨pq, h⟩ := hex; ⟨pq, by simp [T, h]⟩
  obtain ⟨pq, hpqT, hmax⟩ := T.exists_max_image (fun pq => pq.1.1) hT
  have hpq : Y pq ≠ 0 := (Finset.mem_filter.mp hpqT).2
  set i := cls sz pq.1.1 with hi
  set l := start sz (i : ℕ) with hl
  have hblock : ∀ p' q' : Fin (∑ i, sz i), l ≤ (p' : ℕ) → l ≤ (q' : ℕ) →
      RealLeviChart.lower sz Y p' q' = (1 : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) p' q' := by
    intro p' q' _ hq'
    by_cases h : cls sz q' < cls sz p'
    · have hq'i : i ≤ cls sz q' := (start_le_iff sz i q').mp hq'
      have hpp' : pq.1.1 < p' := lt_of_cls_lt sz (lt_of_le_of_lt hq'i h)
      have hz : Y ⟨(p', q'), h⟩ = 0 := by
        by_contra hz
        have := hmax ⟨(p', q'), h⟩ (by simp [T, hz])
        exact absurd this (not_le.mpr hpp')
      simp only [RealLeviChart.lower, Matrix.of_apply, h, ↓reduceDIte]
      rw [hz, Matrix.one_apply_ne (fun e => by rw [e] at h; exact lt_irrefl _ h)]
    · exact lower_apply_of_not_lt sz Y h
  have hgram := gram_of_block_one l hblock
  have hLL : lowerLeft l (RealLeviChart.lower sz Y) ≠ 0 := by
    intro h0
    have hpl : l ≤ (pq.1.1 : ℕ) := (start_le_iff sz i pq.1.1).mpr le_rfl
    have hql : (pq.1.2 : ℕ) < l := by
      by_contra hq
      exact absurd ((start_le_iff sz i pq.1.2).mp (not_lt.mp hq)) (not_le.mpr pq.2)
    have h1 := congrFun (congrFun h0 pq.1.1) pq.1.2
    simp only [lowerLeft, Matrix.of_apply, Matrix.zero_apply] at h1
    rw [ite_eq_left ⟨hpl, hql⟩] at h1
    simp only [RealLeviChart.lower, Matrix.of_apply, pq.2, ↓reduceDIte] at h1
    exact hpq h1
  have hgt : 1 < GramFormula.gram l (RealLeviChart.lower sz Y) := by
    rw [hgram]
    exact one_lt_det_one_add hLL
  rw [beta_eq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i, (GramFormula.gram (start sz (j : ℕ)) (RealLeviChart.lower sz Y))⁻¹ ≤ 1 :=
    Finset.prod_le_one₀
      (fun j _ => (inv_pos.mpr (zero_lt_one.trans_le (one_le_gram_lower sz Y _))).le)
      fun j _ => inv_le_one_of_one_le₀ (one_le_gram_lower sz Y _)
  calc (GramFormula.gram l (RealLeviChart.lower sz Y))⁻¹ *
        ∏ j ∈ Finset.univ.erase i, (GramFormula.gram (start sz (j : ℕ)) (RealLeviChart.lower sz Y))⁻¹ ≤
      (GramFormula.gram l (RealLeviChart.lower sz Y))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hrest (inv_pos.mpr (zero_lt_one.trans hgt)).le
    _ < 1 := by
      rw [mul_one]
      exact inv_lt_one_of_one_lt₀ hgt

/-- **Gap.** Outside every ball around `0`, `β` is bounded by a constant `< 1`. -/
theorem exists_gap {δ : ℝ} (hδ : 0 < δ) :
    ∃ q < 1, ∀ X : Coord sz → ℝ, δ ≤ ‖X‖ → beta sz X ≤ q := by
  have hred : ∀ X : Coord sz → ℝ, δ ≤ ‖X‖ → ∃ Y : Coord sz → ℝ, ‖Y‖ = δ ∧
      beta sz X ≤ beta sz Y := by
    intro X hX
    have hX0 : 0 < ‖X‖ := hδ.trans_le hX
    set S := ‖X‖ / δ with hS
    have hS1 : 1 ≤ S := (one_le_div hδ).mpr hX
    have hcont : ContinuousOn (fun s => ‖scaleCoord sz s X‖) (Set.Icc 1 S) :=
      ((continuousOn_scaleCoord X).mono fun s hs => zero_lt_one.trans_le hs.1).norm
    have h1 : ‖scaleCoord sz S X‖ ≤ δ := by
      refine (norm_scaleCoord_le hS1 X).trans (le_of_eq ?_)
      rw [hS]
      field_simp
    have h0 : δ ≤ ‖scaleCoord sz 1 X‖ := by rw [scaleCoord_one]; exact hX
    obtain ⟨s, hs, hseq⟩ := intermediate_value_Icc' hS1 hcont ⟨h1, h0⟩
    exact ⟨scaleCoord sz s X, hseq, beta_le_beta_scale hs.1 X⟩
  by_cases hne : (Metric.sphere (0 : Coord sz → ℝ) δ).Nonempty
  · obtain ⟨Y0, hY0, hmax⟩ := (isCompact_sphere (0 : Coord sz → ℝ) δ).exists_isMaxOn hne
      continuous_beta.continuousOn
    have hY0' : Y0 ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hY0
      exact hδ.ne hY0
    refine ⟨beta sz Y0, beta_lt_one hY0', fun X hX => ?_⟩
    obtain ⟨Y, hY, hXY⟩ := hred X hX
    exact hXY.trans (isMaxOn_iff.mp hmax Y (mem_sphere_zero_iff_norm.mpr hY))
  · refine ⟨0, zero_lt_one, fun X hX => ?_⟩
    obtain ⟨Y, hY, -⟩ := hred X hX
    exact absurd ⟨Y, mem_sphere_zero_iff_norm.mpr hY⟩ hne

end Beta

end RealLeviBump

end Langlands.Archimedean
