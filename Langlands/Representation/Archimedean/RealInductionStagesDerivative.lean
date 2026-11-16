import Langlands.Representation.Archimedean.RealInductionStagesInduce

/-!
# Induced maps and right derivatives

Let `T : KFin r ds' → KFin r ds` commute exactly with right translation by `O(r)`, and let
`M` be a subspace of `KFin r ds` such that `T R(Z) - R(Z) T` maps into `M` for every real
`r × r` matrix `Z`. Then for every real `n × n` matrix `X`, every `F` and every `κ ∈ O(n)`,

  `σ_κ (Ind T (R(X) F) - R(X) (Ind T F)) ∈ M`

(`sliceK_ind_lie_sub_mem`). The proof reduces to `κ = 1` and splits `X = A + P Z Pᵀ + W`
with `A` upper triangular and zero on the middle block, `P Z Pᵀ` in the middle block and `W`
antisymmetric:

* along `A`, the right derivative of every principal-series function acts on the slice at `1`
  by the scalar `∑ αᵢ Aᵢᵢ` (`slice_rightDerivative_upper`), the same for `ds` and `ds'`;
* along `P Z Pᵀ`, the slice at `1` of the right derivative is `R(Z) σ₁ - m σ₁` with a scalar
  `m` independent of the blocks (`slice_rightDerivative_mid`);
* along `W`, `Ind T` commutes exactly with `R(W)` (`sliceK_lie_ind_skew`), by differentiating
  the exact `O(n)`-equivariance along `t ↦ exp(t W)`.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Manifold ContDiff Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false

namespace Langlands.Archimedean

namespace InductionStages

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean GramFormula
  PrincipalSeriesExtension

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

/-! ## Matrix identities -/

section Matrices

variable {n a r : ℕ}

theorem embMat_transpose_mul_apply (h : a + r ≤ n) {m : Type*} (M : Matrix (Fin n) m ℝ)
    (k : Fin r) (l : m) : ((embMat n a r)ᵀ * M) k l = M (idx h k) l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (idx h k)]
  · simp [embMat, idx]
  · intro i _ hi
    have : ¬ ((i : ℕ) = a + k) := fun e => hi (Fin.ext e)
    simp [embMat, this]
  · simp

theorem mul_embMat_apply (h : a + r ≤ n) {m : Type*} (M : Matrix m (Fin n) ℝ)
    (l : m) (k : Fin r) : (M * embMat n a r) l k = M l (idx h k) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (idx h k)]
  · simp [embMat, idx]
  · intro i _ hi
    have : ¬ ((i : ℕ) = a + k) := fun e => hi (Fin.ext e)
    simp [embMat, this]
  · simp

/-- `ι(y) P = P y`. -/
theorem blockMat_mul_embMat (h : a + r ≤ n) (y : Matrix (Fin r) (Fin r) ℝ) :
    blockMat n a r y * embMat n a r = embMat n a r * y := by
  simp only [blockMat, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
    embMat_transpose_mul_embMat h, Matrix.mul_one, Matrix.mul_sub]
  abel

/-- `ι(y) (P Z Pᵀ) = P (y Z) Pᵀ`. -/
theorem blockMat_mul_mid (h : a + r ≤ n) (y Z : Matrix (Fin r) (Fin r) ℝ) :
    blockMat n a r y * (embMat n a r * Z * (embMat n a r)ᵀ) =
      embMat n a r * (y * Z) * (embMat n a r)ᵀ := by
  simp only [← Matrix.mul_assoc, blockMat_mul_embMat h]

theorem mid_apply_idx (h : a + r ≤ n) (Z : Matrix (Fin r) (Fin r) ℝ) (k l : Fin r) :
    (embMat n a r * Z * (embMat n a r)ᵀ) (idx h k) (idx h l) = Z k l := by
  rw [mul_embMat_transpose_apply_idx h, embMat_mul_apply_idx h]

theorem mid_apply_of_not_isMid_left (Z : Matrix (Fin r) (Fin r) ℝ) {i : Fin n}
    (hi : ¬IsMid a r i) (j : Fin n) : (embMat n a r * Z * (embMat n a r)ᵀ) i j = 0 := by
  rw [Matrix.mul_assoc, embMat_mul_apply_of_not_isMid _ hi]

theorem mid_apply_of_not_isMid_right (Z : Matrix (Fin r) (Fin r) ℝ) (i : Fin n) {j : Fin n}
    (hj : ¬IsMid a r j) : (embMat n a r * Z * (embMat n a r)ᵀ) i j = 0 :=
  mul_embMat_transpose_apply_of_not_isMid _ _ hj

/-- The middle block `Pᵀ Y P` of an `n × n` matrix `Y`. -/
def midBlock (n a r : ℕ) (Y : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  (embMat n a r)ᵀ * Y * embMat n a r

theorem midBlock_apply (h : a + r ≤ n) (Y : Matrix (Fin n) (Fin n) ℝ) (k l : Fin r) :
    midBlock n a r Y k l = Y (idx h k) (idx h l) := by
  rw [midBlock, mul_embMat_apply h, embMat_transpose_mul_apply h]

/-- The entries of `Y` strictly below the diagonal and outside the middle block. -/
def lowerOut (a r : ℕ) (Y : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if j < i ∧ ¬(IsMid a r i ∧ IsMid a r j) then Y i j else 0

/-- The antisymmetric part `L - Lᵀ`, `L = lowerOut a r Y`. -/
def skewOut (a r : ℕ) (Y : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  lowerOut a r Y - (lowerOut a r Y)ᵀ

theorem skewOut_transpose (Y : Matrix (Fin n) (Fin n) ℝ) :
    (skewOut a r Y)ᵀ = -skewOut a r Y := by
  simp only [skewOut, Matrix.transpose_sub, Matrix.transpose_transpose, neg_sub]

/-- The remaining part `Y - P (Pᵀ Y P) Pᵀ - skewOut a r Y`. -/
def upperOut (n a r : ℕ) (Y : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Y - embMat n a r * midBlock n a r Y * (embMat n a r)ᵀ - skewOut a r Y

theorem eq_upperOut_add (Y : Matrix (Fin n) (Fin n) ℝ) :
    Y = upperOut n a r Y + embMat n a r * midBlock n a r Y * (embMat n a r)ᵀ +
      skewOut a r Y := by
  simp only [upperOut]
  abel

theorem upperOut_apply_of_lt (h : a + r ≤ n) (Y : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (hij : j < i) : upperOut n a r Y i j = 0 := by
  have hji : ¬ i < j := fun e => lt_asymm hij e
  simp only [upperOut, skewOut, Matrix.sub_apply, Matrix.transpose_apply, lowerOut,
    Matrix.of_apply, hji, false_and, ite_false, sub_zero]
  by_cases hm : IsMid a r i ∧ IsMid a r j
  · obtain ⟨k, rfl⟩ := exists_idx_of_isMid h hm.1
    obtain ⟨l, rfl⟩ := exists_idx_of_isMid h hm.2
    rw [mid_apply_idx h, midBlock_apply h]
    simp [hm]
  · have h0 : (embMat n a r * midBlock n a r Y * (embMat n a r)ᵀ) i j = 0 := by
      by_cases hi : IsMid a r i
      · exact mid_apply_of_not_isMid_right _ _ fun hj => hm ⟨hi, hj⟩
      · exact mid_apply_of_not_isMid_left _ hi _
    rw [h0]
    simp [hij, hm]

theorem upperOut_apply_mid (h : a + r ≤ n) (Y : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (hi : IsMid a r i) (hj : IsMid a r j) : upperOut n a r Y i j = 0 := by
  simp only [upperOut, skewOut, Matrix.sub_apply, Matrix.transpose_apply, lowerOut,
    Matrix.of_apply]
  obtain ⟨k, rfl⟩ := exists_idx_of_isMid h hi
  obtain ⟨l, rfl⟩ := exists_idx_of_isMid h hj
  rw [mid_apply_idx h, midBlock_apply h]
  simp [isMid_idx h]

/-- Conjugating a matrix that is upper triangular and zero on the middle block by `ι(y)`
does not change its entries on and below the diagonal. -/
theorem blockMat_conj_apply (h : a + r ≤ n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA1 : ∀ i j : Fin n, j < i → A i j = 0)
    (hA2 : ∀ i j : Fin n, IsMid a r i → IsMid a r j → A i j = 0)
    (y y' : Matrix (Fin r) (Fin r) ℝ) {k l : Fin n} (hlk : l ≤ k) :
    (blockMat n a r y * A * blockMat n a r y') k l = A k l := by
  set P := embMat n a r with hP
  have hU : (Pᵀ * A) * P = 0 := by
    ext p q
    rw [mul_embMat_apply h, embMat_transpose_mul_apply h, Matrix.zero_apply]
    exact hA2 _ _ (isMid_idx h p) (isMid_idx h q)
  have hexp : blockMat n a r y * A * blockMat n a r y' =
      A + P * ((y - 1) * (Pᵀ * A)) + (A * P) * (y' - 1) * Pᵀ +
        P * (y - 1) * ((Pᵀ * A) * P) * (y' - 1) * Pᵀ := by
    simp only [blockMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    abel
  rw [hexp, hU, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, add_zero, Matrix.add_apply,
    Matrix.add_apply]
  have h1 : (P * ((y - 1) * (Pᵀ * A)) : Matrix (Fin n) (Fin n) ℝ) k l = 0 := by
    by_cases hk : IsMid a r k
    · obtain ⟨k', rfl⟩ := exists_idx_of_isMid h hk
      rw [hP, embMat_mul_apply_idx h, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [embMat_transpose_mul_apply h]
      by_cases hl : IsMid a r l
      · rw [hA2 _ _ (isMid_idx h m) hl, mul_zero]
      · have : l < idx h m := by
          rw [Fin.lt_def, idx_val]
          unfold IsMid at hk hl
          rw [Fin.le_def, idx_val] at hlk
          omega
        rw [hA1 _ _ this, mul_zero]
    · exact embMat_mul_apply_of_not_isMid _ hk _
  have h2 : ((A * P) * (y' - 1) * Pᵀ : Matrix (Fin n) (Fin n) ℝ) k l = 0 := by
    by_cases hl : IsMid a r l
    · obtain ⟨l', rfl⟩ := exists_idx_of_isMid h hl
      rw [hP, mul_embMat_transpose_apply_idx h, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [mul_embMat_apply h]
      by_cases hk : IsMid a r k
      · rw [hA2 _ _ hk (isMid_idx h m), zero_mul]
      · have : idx h m < k := by
          rw [Fin.lt_def, idx_val]
          unfold IsMid at hk hl
          rw [Fin.le_def] at hlk
          have := m.isLt
          omega
        rw [hA1 _ _ this, zero_mul]
    · exact mul_embMat_transpose_apply_of_not_isMid _ _ hl
  rw [h1, h2, add_zero, add_zero]

end Matrices

/-! ## Smoothness and right derivatives of slices -/

section SliceDerivative

variable {n a r : ℕ}

theorem contMDiff_sliceFactor : ContMDiff (matrixModel ℝ r) 𝓘(ℝ, ℂ) ∞ (sliceFactor n a r) :=
  contMDiff_of_contDiffOn
    (ψ := fun y : Matrix (Fin r) (Fin r) ℝ => ((|y.det| : ℝ) : ℂ) ^ (-sliceExponent n a r))
    (fun _ hy => (contDiffAt_sliceFactor hy).contDiffWithinAt) fun _ => rfl

theorem contDiff_blockMat : ContDiff ℝ ∞ (blockMat n a r) := by
  have h := contDiff_blockMat_mul (n := n) (a := a) (r := r) 1
  simpa only [Matrix.mul_one] using h

theorem contMDiff_comp_blockEmb (h : a + r ≤ n) {G : Langlands.GeneralLinear n ℝ → ℂ}
    (hG : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ G) :
    ContMDiff (matrixModel ℝ r) 𝓘(ℝ, ℂ) ∞ (fun g => G (blockEmb h g)) := by
  refine contMDiff_of_contDiffOn (ψ := fun y => unitsExtension G (blockMat n a r y)) ?_ ?_
  · intro y hy
    refine ContDiffAt.contDiffWithinAt ?_
    have hu : IsUnit (blockMat n a r y) := by
      obtain ⟨g, rfl⟩ := hy
      exact ⟨blockEmb h g, rfl⟩
    have hext := (contDiffOn_unitsExtension hG).contDiffAt
      (isOpen_setOf_isUnit_matrix.mem_nhds hu)
    exact hext.comp y contDiff_blockMat.contDiffAt
  · intro g
    rw [← blockEmb_val h g, unitsExtension_val]

/-- The linear part `y ↦ P y Pᵀ` of the affine map `blockMat`. -/
def midLin (n a r : ℕ) : Matrix (Fin r) (Fin r) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => embMat n a r * y * (embMat n a r)ᵀ
      map_add' := fun y z => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c y => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }

theorem midLin_apply (y : Matrix (Fin r) (Fin r) ℝ) :
    midLin n a r y = embMat n a r * y * (embMat n a r)ᵀ :=
  rfl

theorem hasFDerivAt_blockMat (y : Matrix (Fin r) (Fin r) ℝ) :
    HasFDerivAt (blockMat n a r) (midLin n a r) y := by
  have heq : blockMat n a r = fun y => (1 - embMat n a r * (embMat n a r)ᵀ) + midLin n a r y := by
    funext y
    simp only [blockMat, midLin_apply, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  rw [heq]
  exact (midLin n a r).hasFDerivAt.const_add _

/-- **Chain rule.** `R(Z) (G ∘ ι) (g) = R(P Z Pᵀ) G (ι g)`. -/
theorem rightDerivative_comp_blockEmb (h : a + r ≤ n) {G : Langlands.GeneralLinear n ℝ → ℂ}
    (hG : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ G) (Z : Matrix (Fin r) (Fin r) ℝ)
    (g : Langlands.GeneralLinear r ℝ) :
    rightDerivative (matrixModel ℝ r) Z (fun g => G (blockEmb h g)) g =
      rightDerivative (matrixModel ℝ n) (embMat n a r * Z * (embMat n a r)ᵀ) G
        (blockEmb h g) := by
  rw [rightDerivative_eq_fderiv (contMDiff_comp_blockEmb h hG),
    rightDerivative_eq_fderiv hG, blockEmb_val, blockMat_mul_mid h]
  have heq : unitsExtension (fun g => G (blockEmb h g)) =ᶠ[𝓝 (g : Matrix (Fin r) (Fin r) ℝ)]
      fun y => unitsExtension G (blockMat n a r y) := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit g)] with y hy
    obtain ⟨u, rfl⟩ := hy
    rw [unitsExtension_val, ← blockEmb_val h u, unitsExtension_val]
  rw [heq.fderiv_eq]
  have hu : IsUnit (blockMat n a r (g : Matrix (Fin r) (Fin r) ℝ)) := by
    rw [← blockEmb_val h g]
    exact Units.isUnit _
  have hG' : HasFDerivAt (unitsExtension G)
      (fderiv ℝ (unitsExtension G) (blockMat n a r (g : Matrix (Fin r) (Fin r) ℝ)))
      (blockMat n a r (g : Matrix (Fin r) (Fin r) ℝ)) :=
    (differentiableAt_unitsExtension hG hu).hasFDerivAt
  have hc : HasFDerivAt (fun y => unitsExtension G (blockMat n a r y))
      ((fderiv ℝ (unitsExtension G) (blockMat n a r (g : Matrix (Fin r) (Fin r) ℝ))).comp
        (midLin n a r)) (g : Matrix (Fin r) (Fin r) ℝ) :=
    hG'.comp (g : Matrix (Fin r) (Fin r) ℝ) (hasFDerivAt_blockMat _)
  rw [hc.fderiv]
  rfl

/-- **The middle directions.** `σ₁ (R(P Z Pᵀ) G) = R(Z) σ₁ G - m σ₁ G` with
`m = R(Z) ν (1)`. -/
theorem slice_rightDerivative_mid (h : a + r ≤ n) {G : Langlands.GeneralLinear n ℝ → ℂ}
    (hG : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ G) (Z : Matrix (Fin r) (Fin r) ℝ) :
    slice h 1 (rightDerivative (matrixModel ℝ n) (embMat n a r * Z * (embMat n a r)ᵀ) G) =
      rightDerivative (matrixModel ℝ r) Z (slice h 1 G) -
        rightDerivative (matrixModel ℝ r) Z (sliceFactor n a r) 1 • slice h 1 G := by
  have hν := contMDiff_sliceFactor (n := n) (a := a) (r := r)
  have hGb := contMDiff_comp_blockEmb h hG
  have hs : slice h 1 G = fun g => sliceFactor n a r g * G (blockEmb h g) := by
    funext g
    rw [slice_apply, mul_one]
  funext g
  have hprod := RealPrincipalSeriesDuality.rightDerivative_mul_fun hν hGb Z g
  have hνg : rightDerivative (matrixModel ℝ r) Z (sliceFactor n a r) g =
      sliceFactor n a r g * rightDerivative (matrixModel ℝ r) Z (sliceFactor n a r) 1 := by
    have := rightDerivative_mul_left_of_eq hν (a := g) (c := sliceFactor n a r g)
      (fun g' => sliceFactor_mul g g') Z 1
    rwa [mul_one] at this
  rw [hs, Pi.sub_apply, Pi.smul_apply, hprod, hνg, slice_apply, mul_one,
    rightDerivative_comp_blockEmb h hG Z g, smul_eq_mul]
  ring

/-- **The upper triangular directions.** For `A` upper triangular and zero on the middle
block and `G` in a principal series with `χᵢ(eˣ) = e^{τᵢ x}`,
`σ₁ (R(A) G) = (∑ αᵢ Aᵢᵢ) σ₁ G` with `αᵢ = τᵢ + (n - 1)/2 - i`. -/
theorem slice_rightDerivative_upper (h : a + r ≤ n) {χ : ℕ → ℝˣ → ℂ} {τ : Fin n → ℂ}
    (hχ : ∀ (i : Fin n) (x : ℝ),
      χ i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = Complex.exp (τ i * x))
    {G : Langlands.GeneralLinear n ℝ → ℂ} (hG : G ∈ principalSeries ℝ n χ)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA1 : ∀ i j : Fin n, j < i → A i j = 0)
    (hA2 : ∀ i j : Fin n, IsMid a r i → IsMid a r j → A i j = 0) :
    slice h 1 (rightDerivative (matrixModel ℝ n) A G) =
      (∑ i : Fin n, (τ i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) * (A i i : ℂ)) •
        slice h 1 G := by
  have hGs := ((mem_principalSeries_iff ℝ n χ G).mp hG).1
  have hα := RealBlockDerivative.isExpEquivariant_of_mem_principalSeries hχ hG
  funext g
  set B : Matrix (Fin n) (Fin n) ℝ := blockMat n a r (g : Matrix (Fin r) (Fin r) ℝ) with hB
  set B' : Matrix (Fin n) (Fin n) ℝ :=
    blockMat n a r ((g⁻¹ : Langlands.GeneralLinear r ℝ) : Matrix (Fin r) (Fin r) ℝ) with hB'
  set C : Matrix (Fin n) (Fin n) ℝ := B * A * B' with hC
  have hBB : B' * B = 1 := by
    rw [hB, hB', ← blockMat_mul h, ← Units.val_mul, inv_mul_cancel, Units.val_one, blockMat_one]
  have hCB : B * A = C * B := by
    rw [hC, Matrix.mul_assoc (B * A), hBB, Matrix.mul_one]
  have hCl : ∀ k l : Fin n, l ≤ k → C k l = A k l := fun k l hlk =>
    blockMat_conj_apply h hA1 hA2 _ _ hlk
  have hCu : C.IsUpperTriangular := fun i j hij => by
    rw [hCl i j hij.le]
    exact hA1 i j hij
  have key := RealBlockDerivative.fderiv_upperTriangular_of_isExpEquivariant hGs hα
    (blockEmb h g) hCu
  rw [blockEmb_val, ← hB, ← hCB] at key
  simp only [Pi.smul_apply, smul_eq_mul, slice_apply, mul_one]
  rw [rightDerivative_eq_fderiv hGs, blockEmb_val, ← hB, key]
  have hdiag : ∀ i, C i i = A i i := fun i => hCl i i le_rfl
  simp only [hdiag]
  ring

end SliceDerivative

/-! ## The curve `t ↦ exp(t W)` in `O(n)` -/

section Skew

variable {n : ℕ}

/-- `t ↦ exp(t W)` as a curve in the orthogonal group, for an antisymmetric `W`. -/
def expCurve (W : Matrix (Fin n) (Fin n) ℝ) (hW : Wᵀ = -W) (t : ℝ) :
    Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨NormedSpace.exp (t • W), NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.smul_mem t (by
      rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, hW]))⟩

theorem expCurve_zero (W : Matrix (Fin n) (Fin n) ℝ) (hW : Wᵀ = -W) : expCurve W hW 0 = 1 :=
  Subtype.ext (by simp [expCurve])

theorem hasDerivAt_expCurve (W : Matrix (Fin n) (Fin n) ℝ) (hW : Wᵀ = -W) (i j : Fin n) :
    HasDerivAt (fun t => (expCurve W hW t : Matrix (Fin n) (Fin n) ℝ) i j) (W i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) W (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

end Skew

/-! ## The derivative defect of the induced map -/

section Defect

variable {n a r : ℕ} {pre ds ds' post : List RealBlock}
  (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank ds = r) (hr' : realRank ds' = r)
  (hn : realRank (pre ++ ds ++ post) = n) {T : KFin r ds' →ₗ[ℂ] KFin r ds}
  (hT : ∀ k f, T (kRep r ds' k f) = kRep r ds k (T f))

theorem lie_add (r : ℕ) (ds : List RealBlock) (X Y : Matrix (Fin r) (Fin r) ℝ) :
    lie r ds (X + Y) = lie r ds X + lie r ds Y := by
  simp only [lie, TensorProduct.tmul_add, map_add]

theorem sliceK_one_apply_coe {L : List RealBlock} (F : KFin n (pre ++ L ++ post))
    (hL : realRank L = r) :
    ((sliceK h ha hL 1 F : KFin r L) : Langlands.GeneralLinear r ℝ → ℂ) =
      slice h 1 (F : Langlands.GeneralLinear n ℝ → ℂ) :=
  rfl

/-- **The antisymmetric directions.** `σ₁ (R(W) Ind T F) = T σ₁ (R(W) F)`. -/
theorem sliceK_lie_ind_skew (W : Matrix (Fin n) (Fin n) ℝ) (hW : Wᵀ = -W)
    (F : KFin n (pre ++ ds' ++ post)) :
    sliceK h ha hr 1 (lie n (pre ++ ds ++ post) W (ind h ha hr hr' hn T hT F)) =
      T (sliceK h ha hr' 1 (lie n (pre ++ ds' ++ post) W F)) := by
  apply Subtype.ext
  funext y
  let ℓ : KFin n (pre ++ ds ++ post) →ₗ[ℂ] ℂ :=
    (LinearMap.proj y) ∘ₗ (KFin r ds).subtype ∘ₗ sliceK h ha hr 1
  let ℓ' : KFin n (pre ++ ds' ++ post) →ₗ[ℂ] ℂ :=
    (LinearMap.proj y) ∘ₗ (KFin r ds).subtype ∘ₗ T ∘ₗ sliceK h ha hr' 1
  have d1 := (isRealGKModule_realStandardModule n (pre ++ ds ++ post)).2.2.1 (expCurve W hW) W
    (expCurve_zero W hW) (hasDerivAt_expCurve W hW) (ind h ha hr hr' hn T hT F) ℓ
  have d2 := (isRealGKModule_realStandardModule n (pre ++ ds' ++ post)).2.2.1 (expCurve W hW) W
    (expCurve_zero W hW) (hasDerivAt_expCurve W hW) F ℓ'
  have heq : (fun t => ℓ (realStandardRep n (pre ++ ds ++ post) (expCurve W hW t)
      (ind h ha hr hr' hn T hT F))) =
      fun t => ℓ' (realStandardRep n (pre ++ ds' ++ post) (expCurve W hW t) F) := by
    funext t
    have e1 : realStandardRep n (pre ++ ds ++ post) (expCurve W hW t)
        (ind h ha hr hr' hn T hT F) =
        kRep n (pre ++ ds ++ post) (ofUnitary n (expCurve W hW t))
          (ind h ha hr hr' hn T hT F) := rfl
    have e2 : realStandardRep n (pre ++ ds' ++ post) (expCurve W hW t) F =
        kRep n (pre ++ ds' ++ post) (ofUnitary n (expCurve W hW t)) F := rfl
    simp only [ℓ, ℓ', LinearMap.comp_apply, e1, e2, ← ind_kRep h ha hr hr' hn hT,
      sliceK_ind h ha hr hr' hn hT]
  rw [heq] at d1
  exact d1.unique d2

/-- **The derivative defect at `κ = 1`.** -/
theorem sliceK_one_lie_ind_sub_mem (M : Submodule ℂ (KFin r ds))
    (hM : ∀ (Z : Matrix (Fin r) (Fin r) ℝ) (f : KFin r ds'),
      T (lie r ds' Z f) - lie r ds Z (T f) ∈ M)
    (X : Matrix (Fin n) (Fin n) ℝ) (F : KFin n (pre ++ ds' ++ post)) :
    T (sliceK h ha hr' 1 (lie n (pre ++ ds' ++ post) X F)) -
      sliceK h ha hr 1 (lie n (pre ++ ds ++ post) X (ind h ha hr hr' hn T hT F)) ∈ M := by
  set A := upperOut n a r X with hAdef
  set Z := midBlock n a r X with hZ
  set W := skewOut a r X with hW
  have hX : X = A + embMat n a r * Z * (embMat n a r)ᵀ + W := eq_upperOut_add X
  have hA1 : ∀ i j : Fin n, j < i → A i j = 0 := fun i j hij => upperOut_apply_of_lt h X hij
  have hA2 : ∀ i j : Fin n, IsMid a r i → IsMid a r j → A i j = 0 := fun i j hi hj =>
    upperOut_apply_mid h X hi hj
  set G := ind h ha hr hr' hn T hT F with hGdef
  have hσG : sliceK h ha hr 1 G = T (sliceK h ha hr' 1 F) := sliceK_ind h ha hr hr' hn hT 1 F
  -- the upper triangular part
  set α : List RealBlock → ℂ := fun L => ∑ i : Fin n,
    (realPositionExponent L i + ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) * (A i i : ℂ) with hα
  have hαeq : α (pre ++ ds ++ post) = α (pre ++ ds' ++ post) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : IsMid a r i
    · rw [hA2 i i hi hi]
      simp
    · rw [realPositionExponent_outside ha hr hr' (by unfold IsMid at hi; omega)]
  have hupper : ∀ {L : List RealBlock} (hL : realRank L = r) (H : KFin n (pre ++ L ++ post)),
      sliceK h ha hL 1 (lie n (pre ++ L ++ post) A H) = α (pre ++ L ++ post) • sliceK h ha hL 1 H := by
    intro L hL H
    apply Subtype.ext
    rw [Submodule.coe_smul, sliceK_one_apply_coe, sliceK_one_apply_coe, lie_apply_coe]
    exact slice_rightDerivative_upper h (fun i x => realPositionCharacter_exp _ _ x) H.2.1.1
      hA1 hA2
  have hdA : T (sliceK h ha hr' 1 (lie n (pre ++ ds' ++ post) A F)) -
      sliceK h ha hr 1 (lie n (pre ++ ds ++ post) A G) = 0 := by
    rw [hupper hr' F, hupper hr G, map_smul, hσG, hαeq, sub_self]
  -- the middle part
  set m : ℂ := rightDerivative (matrixModel ℝ r) Z (sliceFactor n a r) 1 with hm
  have hmid : ∀ {L : List RealBlock} (hL : realRank L = r) (H : KFin n (pre ++ L ++ post)),
      sliceK h ha hL 1 (lie n (pre ++ L ++ post) (embMat n a r * Z * (embMat n a r)ᵀ) H) =
        lie r L Z (sliceK h ha hL 1 H) - m • sliceK h ha hL 1 H := by
    intro L hL H
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_smul, lie_apply_coe, sliceK_one_apply_coe,
      sliceK_one_apply_coe, lie_apply_coe]
    exact slice_rightDerivative_mid h H.2.1.1.1 Z
  have hdZ : T (sliceK h ha hr' 1 (lie n (pre ++ ds' ++ post)
      (embMat n a r * Z * (embMat n a r)ᵀ) F)) -
      sliceK h ha hr 1 (lie n (pre ++ ds ++ post) (embMat n a r * Z * (embMat n a r)ᵀ) G) =
      T (lie r ds' Z (sliceK h ha hr' 1 F)) - lie r ds Z (T (sliceK h ha hr' 1 F)) := by
    rw [hmid hr' F, hmid hr G, map_sub, map_smul, hσG]
    abel
  -- the antisymmetric part
  have hdW : T (sliceK h ha hr' 1 (lie n (pre ++ ds' ++ post) W F)) -
      sliceK h ha hr 1 (lie n (pre ++ ds ++ post) W G) = 0 := by
    rw [sliceK_lie_ind_skew h ha hr hr' hn hT W (skewOut_transpose X) F, sub_self]
  have hsplit : T (sliceK h ha hr' 1 (lie n (pre ++ ds' ++ post) X F)) -
      sliceK h ha hr 1 (lie n (pre ++ ds ++ post) X G) =
      (T (sliceK h ha hr' 1 (lie n (pre ++ ds' ++ post) A F)) -
        sliceK h ha hr 1 (lie n (pre ++ ds ++ post) A G)) +
      (T (sliceK h ha hr' 1 (lie n (pre ++ ds' ++ post)
        (embMat n a r * Z * (embMat n a r)ᵀ) F)) -
        sliceK h ha hr 1 (lie n (pre ++ ds ++ post) (embMat n a r * Z * (embMat n a r)ᵀ) G)) +
      (T (sliceK h ha hr' 1 (lie n (pre ++ ds' ++ post) W F)) -
        sliceK h ha hr 1 (lie n (pre ++ ds ++ post) W G)) := by
    conv_lhs => rw [hX]
    simp only [lie_add, LinearMap.add_apply, map_add]
    abel
  rw [hsplit, hdA, hdZ, hdW, zero_add, add_zero]
  exact hM Z _

/-- **The derivative defect.** `σ_κ (Ind T (R(X) F) - R(X) (Ind T F)) ∈ M` for `κ ∈ O(n)`. -/
theorem sliceK_ind_lie_sub_mem (M : Submodule ℂ (KFin r ds))
    (hM : ∀ (Z : Matrix (Fin r) (Fin r) ℝ) (f : KFin r ds'),
      T (lie r ds' Z f) - lie r ds Z (T f) ∈ M)
    (X : Matrix (Fin n) (Fin n) ℝ) (F : KFin n (pre ++ ds' ++ post)) (κ : unitaryCompact ℝ n) :
    sliceK h ha hr κ (ind h ha hr hr' hn T hT (lie n (pre ++ ds' ++ post) X F) -
      lie n (pre ++ ds ++ post) X (ind h ha hr hr' hn T hT F)) ∈ M := by
  have hκ : ∀ G : KFin n (pre ++ ds ++ post),
      sliceK h ha hr κ G = sliceK h ha hr 1 (kRep n (pre ++ ds ++ post) κ G) := fun G => by
    rw [sliceK_kRep, one_mul]
  rw [hκ, map_sub, map_sub, ← ind_kRep h ha hr hr' hn hT, kRep_lie, kRep_lie,
    ← ind_kRep h ha hr hr' hn hT, sliceK_ind h ha hr hr' hn hT]
  exact sliceK_one_lie_ind_sub_mem h ha hr hr' hn hT M hM _ _

end Defect

end InductionStages

end Langlands.Archimedean
