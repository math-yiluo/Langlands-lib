import Langlands.Representation.Archimedean.RealLeviBlockDecomposition
import Langlands.Representation.Archimedean.RealLeviChartIntegrable
import Langlands.Representation.Archimedean.RealBlockChartBound
import Langlands.Representation.Archimedean.JacquetLimit

/-!
# The two-block Levi embedding `GL_a × GL_M → GL_{a+M}`

Tools for the proof of `RealLeviParabolicIntegrationStatement`.

* `dg A B = diag(A, B)` of size `a + M` and the group homomorphism
  `dgGL : GL_a(ℝ) × GL_M(ℝ) →* GL_{a+M}(ℝ)`.
* The Levi slices `sliceL F y g = F(diag(g, 1) y) |det g|^{-M}` on `GL_a(ℝ)` and
  `sliceR F y h = F(diag(1, h) y) |det h|^a` on `GL_M(ℝ)` of a smooth function `F` on
  `GL_{a+M}(ℝ)` with `F(diag(t) u g) = δ_B(t) F(g)` are smooth with the same property for the
  Borel subgroups of `GL_a` and `GL_M` (`sliceL_covariant`, `sliceR_covariant`).
* The Gram determinants of `diag(A, B)`: `G_l = G_l(A) det(B Bᵀ)` for `l ≤ a` and
  `G_{a+r} = G_r(B)`.
* The growth bound `‖F(y κ)‖ ≤ C ∏_l G_l(y)^{-1}` for `det(y)² = 1` and `κ ∈ O(N)`
  (`norm_le_gram_inv`), and the integrability of `X ↦ F(n̄(X) κ)` on the coordinates of the
  opposite unipotent radical of a block function (`integrable_comp_lowerCGL`).
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviTwoBlock

open GramFormula MaximalParabolicIntegration RealLeviChartGram RealLeviChartIntegrable
  Langlands.GeneralLinear

/-! ## Block diagonal matrices -/

section Mat

variable {a M : ℕ}

theorem castAdd_ne_natAdd (i : Fin a) (s : Fin M) : Fin.castAdd M i ≠ Fin.natAdd a s :=
  (natAdd_ne_castAdd s i).symm

/-- `diag(A, B)` of size `a + M`. -/
def dg (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ) :
    Matrix (Fin (a + M)) (Fin (a + M)) ℝ :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B)

@[simp] theorem dg_castAdd_castAdd (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ)
    (i j : Fin a) : dg A B (Fin.castAdd M i) (Fin.castAdd M j) = A i j := by
  simp [dg]

@[simp] theorem dg_castAdd_natAdd (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ)
    (i : Fin a) (s : Fin M) : dg A B (Fin.castAdd M i) (Fin.natAdd a s) = 0 := by
  simp [dg]

@[simp] theorem dg_natAdd_castAdd (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ)
    (r : Fin M) (j : Fin a) : dg A B (Fin.natAdd a r) (Fin.castAdd M j) = 0 := by
  simp [dg]

@[simp] theorem dg_natAdd_natAdd (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ)
    (r s : Fin M) : dg A B (Fin.natAdd a r) (Fin.natAdd a s) = B r s := by
  simp [dg]

theorem dg_mul (A A' : Matrix (Fin a) (Fin a) ℝ) (B B' : Matrix (Fin M) (Fin M) ℝ) :
    dg A B * dg A' B' = dg (A * A') (B * B') := by
  rw [dg, dg, dg, reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv,
    fromBlocks_multiply]
  simp

theorem dg_one : dg (1 : Matrix (Fin a) (Fin a) ℝ) (1 : Matrix (Fin M) (Fin M) ℝ) = 1 := by
  rw [dg, fromBlocks_one, reindex_apply, submatrix_one_equiv]

theorem dg_transpose (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ) :
    (dg A B)ᵀ = dg Aᵀ Bᵀ := by
  rw [dg, dg, reindex_apply, reindex_apply, transpose_submatrix, fromBlocks_transpose]
  simp

theorem det_dg (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ) :
    (dg A B).det = A.det * B.det := by
  rw [dg, det_reindex_self, det_fromBlocks_zero₂₁]

theorem dg_mul_transpose (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ) :
    dg A B * (dg A B)ᵀ = dg (A * Aᵀ) (B * Bᵀ) := by
  rw [dg_transpose, dg_mul]

theorem dg_add (A A' : Matrix (Fin a) (Fin a) ℝ) (B B' : Matrix (Fin M) (Fin M) ℝ) :
    dg (A + A') (B + B') = dg A B + dg A' B' := by
  ext p q
  refine Fin.addCases (fun i => ?_) (fun r => ?_) p <;>
    refine Fin.addCases (fun j => ?_) (fun s => ?_) q <;> simp

theorem dg_smul (c : ℝ) (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ) :
    dg (c • A) (c • B) = c • dg A B := by
  ext p q
  refine Fin.addCases (fun i => ?_) (fun r => ?_) p <;>
    refine Fin.addCases (fun j => ?_) (fun s => ?_) q <;> simp

theorem dg_isUpperTriangular {A : Matrix (Fin a) (Fin a) ℝ} {B : Matrix (Fin M) (Fin M) ℝ}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) : (dg A B).IsUpperTriangular := by
  intro p q hpq
  change q < p at hpq
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left j =>
      rw [dg_castAdd_castAdd]
      exact hA (show j < i by rw [Fin.lt_def] at hpq ⊢; simpa using hpq)
    | right s => rw [dg_castAdd_natAdd]
  | right r =>
    induction q using Fin.addCases with
    | left j => rw [dg_natAdd_castAdd]
    | right s =>
      rw [dg_natAdd_natAdd]
      exact hB ((Fin.natAdd_lt_natAdd_iff a).mp hpq)

/-! ### Gram determinants -/

theorem padS_dg_of_le (S : Matrix (Fin a) (Fin a) ℝ) (T : Matrix (Fin M) (Fin M) ℝ) {l : ℕ}
    (hl : l ≤ a) : padS l (dg S T) = dg (padS l S) T := by
  ext p q
  refine Fin.addCases (fun i => ?_) (fun r => ?_) p <;>
    refine Fin.addCases (fun j => ?_) (fun s => ?_) q <;>
    simp only [padS, of_apply, dg_castAdd_castAdd, dg_castAdd_natAdd, dg_natAdd_castAdd,
      dg_natAdd_natAdd, Fin.val_castAdd, Fin.val_natAdd]
  · by_cases h : l ≤ (i : ℕ) ∧ l ≤ (j : ℕ)
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.castAdd_inj]
  · rw [Matrix.one_apply_ne (castAdd_ne_natAdd i s)]
    simp
  · rw [Matrix.one_apply_ne (natAdd_ne_castAdd r j)]
    simp
  · rw [ite_eq_left ⟨by omega, by omega⟩]

theorem padS_dg_add (S : Matrix (Fin a) (Fin a) ℝ) (T : Matrix (Fin M) (Fin M) ℝ) (r : ℕ) :
    padS (a + r) (dg S T) = dg 1 (padS r T) := by
  ext p q
  refine Fin.addCases (fun i => ?_) (fun s => ?_) p <;>
    refine Fin.addCases (fun j => ?_) (fun t => ?_) q <;>
    simp only [padS, of_apply, dg_castAdd_castAdd, dg_castAdd_natAdd, dg_natAdd_castAdd,
      dg_natAdd_natAdd, Fin.val_castAdd, Fin.val_natAdd]
  · rw [ite_eq_right (fun h => by have := i.2; omega), Matrix.one_apply, Matrix.one_apply]
    simp only [Fin.castAdd_inj]
  · rw [Matrix.one_apply_ne (castAdd_ne_natAdd i t)]
    simp
  · rw [Matrix.one_apply_ne (natAdd_ne_castAdd s j)]
    simp
  · by_cases h : r ≤ (s : ℕ) ∧ r ≤ (t : ℕ)
    · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ⟨by omega, by omega⟩), ite_eq_right h, Matrix.one_apply,
        Matrix.one_apply]
      simp only [Fin.natAdd_inj]

/-- `G_l(diag(A, B)) = G_l(A) det(B Bᵀ)` for `l ≤ a`. -/
theorem gram_dg_of_le (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ) {l : ℕ}
    (hl : l ≤ a) : gram l (dg A B) = gram l A * (B * Bᵀ).det := by
  rw [gram_eq_tm, tm, dg_mul_transpose, padS_dg_of_le _ _ hl, det_dg]
  rfl

/-- `G_{a+r}(diag(A, B)) = G_r(B)`. -/
theorem gram_dg_add (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin M) (Fin M) ℝ) (r : ℕ) :
    gram (a + r) (dg A B) = gram r B := by
  rw [gram_eq_tm, tm, dg_mul_transpose, padS_dg_add, det_dg, det_one, one_mul]
  rfl

end Mat

/-! ## The embedding on `GL` -/

section Group

variable {a M : ℕ}

/-- `(A, B) ↦ diag(A, B)` as a monoid homomorphism of matrices. -/
def dgHom :
    Matrix (Fin a) (Fin a) ℝ × Matrix (Fin M) (Fin M) ℝ →* Matrix (Fin (a + M)) (Fin (a + M)) ℝ where
  toFun p := dg p.1 p.2
  map_one' := dg_one
  map_mul' p q := (dg_mul p.1 q.1 p.2 q.2).symm

/-- `(g, h) ↦ diag(g, h)` from `GL_a(ℝ) × GL_M(ℝ)` to `GL_{a+M}(ℝ)`. -/
def dgGL :
    Langlands.GeneralLinear a ℝ × Langlands.GeneralLinear M ℝ →*
      Langlands.GeneralLinear (a + M) ℝ :=
  (Units.map dgHom).comp MulEquiv.prodUnits.symm.toMonoidHom

@[simp] theorem dgGL_val (p : Langlands.GeneralLinear a ℝ × Langlands.GeneralLinear M ℝ) :
    ((dgGL p : Langlands.GeneralLinear (a + M) ℝ) : Matrix (Fin (a + M)) (Fin (a + M)) ℝ) =
      dg (p.1 : Matrix (Fin a) (Fin a) ℝ) (p.2 : Matrix (Fin M) (Fin M) ℝ) :=
  rfl

theorem dgGL_diagonalUnits_left (t : Fin a → ℝˣ) :
    dgGL ((Iwasawa.diagonalUnits t : Langlands.GeneralLinear a ℝ),
      (1 : Langlands.GeneralLinear M ℝ)) =
      Iwasawa.diagonalUnits (Fin.addCases t (fun _ : Fin M => (1 : ℝˣ)) : Fin (a + M) → ℝˣ) := by
  apply Units.ext
  rw [dgGL_val, Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val, Units.val_one]
  ext p q
  refine Fin.addCases (fun i => ?_) (fun r => ?_) p <;>
    refine Fin.addCases (fun j => ?_) (fun s => ?_) q <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, castAdd_ne_natAdd, natAdd_ne_castAdd]

theorem dgGL_diagonalUnits_right (t : Fin M → ℝˣ) :
    dgGL ((1 : Langlands.GeneralLinear a ℝ),
      (Iwasawa.diagonalUnits t : Langlands.GeneralLinear M ℝ)) =
      Iwasawa.diagonalUnits (Fin.addCases (fun _ : Fin a => (1 : ℝˣ)) t : Fin (a + M) → ℝˣ) := by
  apply Units.ext
  rw [dgGL_val, Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val, Units.val_one]
  ext p q
  refine Fin.addCases (fun i => ?_) (fun r => ?_) p <;>
    refine Fin.addCases (fun j => ?_) (fun s => ?_) q <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, castAdd_ne_natAdd, natAdd_ne_castAdd]

theorem dgGL_mem_upperUnipotent {u : Langlands.GeneralLinear a ℝ} {v : Langlands.GeneralLinear M ℝ}
    (hu : u ∈ upperUnipotent a ℝ) (hv : v ∈ upperUnipotent M ℝ) :
    dgGL (u, v) ∈ upperUnipotent (a + M) ℝ := by
  refine ⟨?_, fun p => ?_⟩
  · change (dg (u : Matrix (Fin a) (Fin a) ℝ) (v : Matrix (Fin M) (Fin M) ℝ)).IsUpperTriangular
    exact dg_isUpperTriangular hu.1 hv.1
  · change dg (u : Matrix (Fin a) (Fin a) ℝ) (v : Matrix (Fin M) (Fin M) ℝ) p p = 1
    induction p using Fin.addCases with
    | left i =>
      rw [dg_castAdd_castAdd]
      exact hu.2 i
    | right r =>
      rw [dg_natAdd_natAdd]
      exact hv.2 r

theorem dgGL_mem_unitaryCompact {k₁ : Langlands.GeneralLinear a ℝ}
    {k₂ : Langlands.GeneralLinear M ℝ} (h₁ : k₁ ∈ unitaryCompact ℝ a)
    (h₂ : k₂ ∈ unitaryCompact ℝ M) : dgGL (k₁, k₂) ∈ unitaryCompact ℝ (a + M) := by
  change dg (k₁ : Matrix (Fin a) (Fin a) ℝ) (k₂ : Matrix (Fin M) (Fin M) ℝ) ∈
    Matrix.unitaryGroup (Fin (a + M)) ℝ
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    dg_transpose, dg_mul, mul_transpose_eq_one_of_mem h₁, mul_transpose_eq_one_of_mem h₂, dg_one]

theorem dgGL_injective :
    Function.Injective (dgGL : Langlands.GeneralLinear a ℝ × Langlands.GeneralLinear M ℝ → _) := by
  intro p q h
  have hv := congrArg (fun g : Langlands.GeneralLinear (a + M) ℝ =>
    (g : Matrix (Fin (a + M)) (Fin (a + M)) ℝ)) h
  simp only [dgGL_val] at hv
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · ext i j
    have := congrFun (congrFun hv (Fin.castAdd M i)) (Fin.castAdd M j)
    simpa using this
  · ext r s
    have := congrFun (congrFun hv (Fin.natAdd a r)) (Fin.natAdd a s)
    simpa using this

/-! ### The modulus character -/

theorem modulusCharacter_addCases_left (t : Fin a → ℝˣ) :
    modulusCharacter (a + M) (Fin.addCases t (fun _ : Fin M => (1 : ℝˣ)) : Fin (a + M) → ℝˣ) =
      modulusCharacter a t * ∏ i, ((|(t i : ℝ)| : ℝ) : ℂ) ^ M := by
  rw [modulusCharacter, modulusCharacter, Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Units.val_one, abs_one, Complex.ofReal_one,
    Complex.one_cpow, Finset.prod_const_one, mul_one, Fin.val_castAdd]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ha : ((|(t i : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr (t i).ne_zero
  have hexp : (((a + M : ℕ) : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) =
      ((a : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) + (M : ℂ) := by
    push_cast
    ring
  rw [hexp, Complex.cpow_add _ _ ha, Complex.cpow_natCast]

theorem modulusCharacter_addCases_right (t : Fin M → ℝˣ) :
    modulusCharacter (a + M) (Fin.addCases (fun _ : Fin a => (1 : ℝˣ)) t : Fin (a + M) → ℝˣ) =
      modulusCharacter M t * ∏ r, (((|(t r : ℝ)| : ℝ) : ℂ) ^ a)⁻¹ := by
  rw [modulusCharacter, modulusCharacter, Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Units.val_one, abs_one, Complex.ofReal_one,
    Complex.one_cpow, Finset.prod_const_one, one_mul, Fin.val_natAdd]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  have ha : ((|(t r : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr (t r).ne_zero
  have hexp : (((a + M : ℕ) : ℂ) - 1 - 2 * ((a + r : ℕ) : ℂ)) =
      ((M : ℂ) - 1 - 2 * ((r : ℕ) : ℂ)) - (a : ℂ) := by
    push_cast
    ring
  rw [hexp, Complex.cpow_sub _ _ ha, Complex.cpow_natCast, div_eq_mul_inv]

theorem det_diagonalUnits_mul (t : Fin a → ℝˣ) (u : upperUnipotent a ℝ)
    (g : Langlands.GeneralLinear a ℝ) :
    ((((Iwasawa.diagonalUnits t : Langlands.GeneralLinear a ℝ) *
      (u : Langlands.GeneralLinear a ℝ) * g : Langlands.GeneralLinear a ℝ)) :
        Matrix (Fin a) (Fin a) ℝ).det =
      (∏ i, (t i : ℝ)) * ((g : Matrix (Fin a) (Fin a) ℝ).det) := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_upperUnipotent,
    Iwasawa.diagonalUnits_val, Matrix.det_diagonal, mul_one]

end Group

/-! ## Smoothness -/

section Smooth

theorem contMDiff_mul_comp {n N : ℕ} {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ F)
    (φ : Langlands.GeneralLinear n ℝ →* Langlands.GeneralLinear N ℝ)
    {Φ : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin N) (Fin N) ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hφ : ∀ g, ((φ g : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) =
      Φ (g : Matrix (Fin n) (Fin n) ℝ))
    (y : Langlands.GeneralLinear N ℝ) {c : Matrix (Fin n) (Fin n) ℝ → ℂ}
    (hc : ContDiffOn ℝ ∞ c {Y | IsUnit Y}) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞
      (fun g => F (φ g * y) * c (g : Matrix (Fin n) (Fin n) ℝ)) := by
  set ψ : Matrix (Fin n) (Fin n) ℝ → ℂ := fun Y =>
    unitsExtension F (Φ Y * (y : Matrix (Fin N) (Fin N) ℝ)) * c Y with hψ
  refine contMDiff_of_contDiffOn (ψ := ψ) ?_ fun g => ?_
  · intro Y hY
    have hY' : IsUnit Y := hY
    have hΦY : Φ Y = ((φ hY'.unit : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) := by
      rw [hφ, IsUnit.unit_spec]
    have hunit : IsUnit (Φ Y * (y : Matrix (Fin N) (Fin N) ℝ)) := by
      rw [hΦY, ← Units.val_mul]
      exact Units.isUnit _
    refine ContDiffWithinAt.mul ?_ (hc Y hY)
    have hmul : ContDiff ℝ ∞ fun Y : Matrix (Fin n) (Fin n) ℝ =>
        Φ Y * (y : Matrix (Fin N) (Fin N) ℝ) := hΦ.mul contDiff_const
    exact (((contDiffOn_unitsExtension hF).contDiffAt
      (isOpen_setOf_isUnit_matrix.mem_nhds hunit)).comp Y hmul.contDiffAt).contDiffWithinAt
  · simp only [hψ]
    rw [← hφ, ← Units.val_mul, unitsExtension_val]

theorem contDiffOn_absDet_pow {n : ℕ} (k : ℕ) :
    ContDiffOn ℝ ∞ (fun Y : Matrix (Fin n) (Fin n) ℝ => ((|Y.det| ^ k : ℝ) : ℂ))
      {Y | IsUnit Y} := by
  intro Y hY
  have hY' : IsUnit Y := hY
  have hdet : Y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Y).mp hY').ne_zero
  have hd : ContDiff ℝ ∞ fun Y : Matrix (Fin n) (Fin n) ℝ => Y.det :=
    PrincipalSeriesExtension.contDiff_det_comp fun p q => PrincipalSeriesExtension.contDiff_entry p q
  have habs : ContDiffAt ℝ ∞ (fun Y : Matrix (Fin n) (Fin n) ℝ => |Y.det|) Y :=
    (contDiffAt_abs hdet).comp Y hd.contDiffAt
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp Y (habs.pow k) |>.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun Z => by simp)).contDiffWithinAt

theorem contDiffOn_absDet_pow_inv {n : ℕ} (k : ℕ) :
    ContDiffOn ℝ ∞ (fun Y : Matrix (Fin n) (Fin n) ℝ => (((|Y.det| ^ k)⁻¹ : ℝ) : ℂ))
      {Y | IsUnit Y} := by
  intro Y hY
  have hY' : IsUnit Y := hY
  have hdet : Y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Y).mp hY').ne_zero
  have hd : ContDiff ℝ ∞ fun Y : Matrix (Fin n) (Fin n) ℝ => Y.det :=
    PrincipalSeriesExtension.contDiff_det_comp fun p q => PrincipalSeriesExtension.contDiff_entry p q
  have habs : ContDiffAt ℝ ∞ (fun Y : Matrix (Fin n) (Fin n) ℝ => |Y.det|) Y :=
    (contDiffAt_abs hdet).comp Y hd.contDiffAt
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp Y ((habs.pow k).inv
    (pow_ne_zero _ (abs_ne_zero.mpr hdet))) |>.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun Z => by simp)).contDiffWithinAt

variable {a M : ℕ}

/-- `A ↦ diag(A, 0)` as a linear map. -/
def dgLinL : Matrix (Fin a) (Fin a) ℝ →ₗ[ℝ] Matrix (Fin (a + M)) (Fin (a + M)) ℝ where
  toFun A := dg A 0
  map_add' A A' := by rw [← dg_add, add_zero]
  map_smul' c A := by rw [RingHom.id_apply, ← dg_smul, smul_zero]

/-- `B ↦ diag(0, B)` as a linear map. -/
def dgLinR : Matrix (Fin M) (Fin M) ℝ →ₗ[ℝ] Matrix (Fin (a + M)) (Fin (a + M)) ℝ where
  toFun B := dg 0 B
  map_add' B B' := by rw [← dg_add, add_zero]
  map_smul' c B := by rw [RingHom.id_apply, ← dg_smul, smul_zero]

theorem contDiff_dg_left (B : Matrix (Fin M) (Fin M) ℝ) :
    ContDiff ℝ ∞ fun A : Matrix (Fin a) (Fin a) ℝ => dg A B := by
  have h : (fun A : Matrix (Fin a) (Fin a) ℝ => dg A B) =
      fun A => (LinearMap.toContinuousLinearMap (dgLinL (M := M))) A + dg 0 B := by
    funext A
    change dg A B = dg A 0 + dg 0 B
    rw [← dg_add, add_zero, zero_add]
  rw [h]
  exact (LinearMap.toContinuousLinearMap dgLinL).contDiff.add contDiff_const

theorem contDiff_dg_right (A : Matrix (Fin a) (Fin a) ℝ) :
    ContDiff ℝ ∞ fun B : Matrix (Fin M) (Fin M) ℝ => dg A B := by
  have h : (fun B : Matrix (Fin M) (Fin M) ℝ => dg A B) =
      fun B => (LinearMap.toContinuousLinearMap (dgLinR (a := a))) B + dg A 0 := by
    funext B
    change dg A B = dg 0 B + dg A 0
    rw [← dg_add, zero_add, add_zero]
  rw [h]
  exact (LinearMap.toContinuousLinearMap dgLinR).contDiff.add contDiff_const

/-- The Levi slice `g ↦ F(diag(g, 1) y) |det g|^{-M}` on `GL_a(ℝ)`. -/
def sliceL (F : Langlands.GeneralLinear (a + M) ℝ → ℂ) (y : Langlands.GeneralLinear (a + M) ℝ)
    (g : Langlands.GeneralLinear a ℝ) : ℂ :=
  F (dgGL (g, 1) * y) * (((|(g : Matrix (Fin a) (Fin a) ℝ).det| ^ M)⁻¹ : ℝ) : ℂ)

/-- The Levi slice `h ↦ F(diag(1, h) y) |det h|^a` on `GL_M(ℝ)`. -/
def sliceR (F : Langlands.GeneralLinear (a + M) ℝ → ℂ) (y : Langlands.GeneralLinear (a + M) ℝ)
    (h : Langlands.GeneralLinear M ℝ) : ℂ :=
  F (dgGL (1, h) * y) * ((|(h : Matrix (Fin M) (Fin M) ℝ).det| ^ a : ℝ) : ℂ)

theorem contMDiff_sliceL {F : Langlands.GeneralLinear (a + M) ℝ → ℂ}
    (hF : ContMDiff (matrixModel ℝ (a + M)) 𝓘(ℝ, ℂ) ∞ F) (y : Langlands.GeneralLinear (a + M) ℝ) :
    ContMDiff (matrixModel ℝ a) 𝓘(ℝ, ℂ) ∞ (sliceL F y) :=
  contMDiff_mul_comp hF (dgGL.comp (MonoidHom.inl _ _)) (contDiff_dg_left 1)
    (fun g => by simp) y (contDiffOn_absDet_pow_inv M)

theorem contMDiff_sliceR {F : Langlands.GeneralLinear (a + M) ℝ → ℂ}
    (hF : ContMDiff (matrixModel ℝ (a + M)) 𝓘(ℝ, ℂ) ∞ F) (y : Langlands.GeneralLinear (a + M) ℝ) :
    ContMDiff (matrixModel ℝ M) 𝓘(ℝ, ℂ) ∞ (sliceR F y) :=
  contMDiff_mul_comp hF (dgGL.comp (MonoidHom.inr _ _)) (contDiff_dg_right 1)
    (fun g => by simp) y (contDiffOn_absDet_pow a)

theorem sliceL_covariant {F : Langlands.GeneralLinear (a + M) ℝ → ℂ}
    (hF : IsModulusCovariant F) (y : Langlands.GeneralLinear (a + M) ℝ) :
    IsModulusCovariant (sliceL F y) := by
  intro t u g
  have hu := dgGL_mem_upperUnipotent u.2 (one_mem (upperUnipotent M ℝ))
  have e : ((Iwasawa.diagonalUnits t : Langlands.GeneralLinear a ℝ) *
      (u : Langlands.GeneralLinear a ℝ) * g, (1 : Langlands.GeneralLinear M ℝ)) =
      ((Iwasawa.diagonalUnits t : Langlands.GeneralLinear a ℝ), (1 : Langlands.GeneralLinear M ℝ)) *
        ((u : Langlands.GeneralLinear a ℝ), (1 : Langlands.GeneralLinear M ℝ)) *
        (g, (1 : Langlands.GeneralLinear M ℝ)) := by
    simp only [Prod.mk_mul_mk, mul_one]
  have h1 : dgGL ((Iwasawa.diagonalUnits t : Langlands.GeneralLinear a ℝ) *
      (u : Langlands.GeneralLinear a ℝ) * g, (1 : Langlands.GeneralLinear M ℝ)) * y =
      (Iwasawa.diagonalUnits (Fin.addCases t (fun _ : Fin M => (1 : ℝˣ)) : Fin (a + M) → ℝˣ) :
        Langlands.GeneralLinear (a + M) ℝ) *
        ((⟨_, hu⟩ : upperUnipotent (a + M) ℝ) : Langlands.GeneralLinear (a + M) ℝ) *
        (dgGL (g, 1) * y) := by
    rw [e, map_mul, map_mul, dgGL_diagonalUnits_left]
    simp only [mul_assoc]
  unfold sliceL
  rw [h1, hF, det_diagonalUnits_mul, modulusCharacter_addCases_left]
  have hP : (∏ i, ((|(t i : ℝ)| : ℝ) : ℂ) ^ M) = (((∏ i, |(t i : ℝ)|) ^ M : ℝ) : ℂ) := by
    push_cast
    rw [Finset.prod_pow]
  have hP0 : ((∏ i, |(t i : ℝ)|) ^ M : ℝ) ≠ 0 :=
    pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i _ => abs_ne_zero.mpr (t i).ne_zero)
  rw [hP, abs_mul, Finset.abs_prod, mul_pow, mul_inv, Complex.ofReal_mul]
  have hP0' : (((∏ i, |(t i : ℝ)|) ^ M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP0
  rw [Complex.ofReal_inv ((∏ i, |(t i : ℝ)|) ^ M)]
  field_simp

theorem sliceR_covariant {F : Langlands.GeneralLinear (a + M) ℝ → ℂ}
    (hF : IsModulusCovariant F) (y : Langlands.GeneralLinear (a + M) ℝ) :
    IsModulusCovariant (sliceR F y) := by
  intro t u h
  have hu := dgGL_mem_upperUnipotent (one_mem (upperUnipotent a ℝ)) u.2
  have e : ((1 : Langlands.GeneralLinear a ℝ), (Iwasawa.diagonalUnits t : Langlands.GeneralLinear M ℝ) *
      (u : Langlands.GeneralLinear M ℝ) * h) =
      ((1 : Langlands.GeneralLinear a ℝ), (Iwasawa.diagonalUnits t : Langlands.GeneralLinear M ℝ)) *
        ((1 : Langlands.GeneralLinear a ℝ), (u : Langlands.GeneralLinear M ℝ)) *
        ((1 : Langlands.GeneralLinear a ℝ), h) := by
    simp only [Prod.mk_mul_mk, mul_one]
  have h1 : dgGL ((1 : Langlands.GeneralLinear a ℝ),
      (Iwasawa.diagonalUnits t : Langlands.GeneralLinear M ℝ) *
      (u : Langlands.GeneralLinear M ℝ) * h) * y =
      (Iwasawa.diagonalUnits (Fin.addCases (fun _ : Fin a => (1 : ℝˣ)) t : Fin (a + M) → ℝˣ) :
        Langlands.GeneralLinear (a + M) ℝ) *
        ((⟨_, hu⟩ : upperUnipotent (a + M) ℝ) : Langlands.GeneralLinear (a + M) ℝ) *
        (dgGL (1, h) * y) := by
    rw [e, map_mul, map_mul, dgGL_diagonalUnits_right]
    simp only [mul_assoc]
  unfold sliceR
  rw [h1, hF, det_diagonalUnits_mul, modulusCharacter_addCases_right]
  have hP : (∏ r, (((|(t r : ℝ)| : ℝ) : ℂ) ^ a)⁻¹) = ((((∏ r, |(t r : ℝ)|) ^ a)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rw [Finset.prod_inv_distrib, Finset.prod_pow]
  have hP0 : ((∏ r, |(t r : ℝ)|) ^ a : ℝ) ≠ 0 :=
    pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun r _ => abs_ne_zero.mpr (t r).ne_zero)
  rw [hP, abs_mul, Finset.abs_prod, mul_pow, Complex.ofReal_mul]
  have hP0' : (((∏ r, |(t r : ℝ)|) ^ a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP0
  rw [Complex.ofReal_inv ((∏ r, |(t r : ℝ)|) ^ a)]
  field_simp

end Smooth

/-! ## Continuity -/

section Continuity

theorem continuous_comp_of_val {X : Type*} [TopologicalSpace X] {N : ℕ}
    {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ F)
    {g : X → Langlands.GeneralLinear N ℝ}
    (hg : Continuous fun x => ((g x : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)) :
    Continuous fun x => F (g x) := by
  have h := (contDiffOn_unitsExtension hF).continuousOn.comp_continuous hg
    (fun x => (g x).isUnit)
  simpa only [Function.comp_def, unitsExtension_val] using h

end Continuity

/-! ## Growth bounds -/

section Growth

/-- `F` is bounded on the compact group `O(N)`. -/
theorem exists_bound {N : ℕ} {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ F) :
    ∃ C, ∀ k ∈ unitaryCompact ℝ N, ‖F k‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((hF.continuous.comp continuous_subtype_val :
      Continuous fun κ : unitaryCompact ℝ N => F κ).continuousOn)
  exact ⟨C, fun k hk => hC ⟨k, hk⟩ trivial⟩

/-- **The growth bound with exponent `−1`.** If `F(diag(t) u g) = δ_B(t) F(g)` and `‖F‖ ≤ C`
on `O(N)`, then `‖F(y κ)‖ ≤ C ∏_l G_l(y)^{-1}` for `det(y)² = 1` and `κ ∈ O(N)`. -/
theorem norm_le_gram_inv {N : ℕ} {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : IsModulusCovariant F) {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℝ N, ‖F k‖ ≤ C)
    (y : Langlands.GeneralLinear N ℝ) (hy : gram 0 (y : Matrix (Fin N) (Fin N) ℝ) = 1)
    {κ : Langlands.GeneralLinear N ℝ} (hκ : κ ∈ unitaryCompact ℝ N) :
    ‖F (y * κ)‖ ≤ C * ∏ l : Fin N, gram (l : ℕ) (y : Matrix (Fin N) (Fin N) ℝ) ^ (-1 : ℝ) := by
  cases N with
  | zero =>
    have : y * κ = κ := Subsingleton.elim _ _
    rw [this, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    exact hC κ hκ
  | succ m =>
    have h := RealBlockChart.norm_le_gram
      (σ := fun l : ℕ => ((m + 1 : ℕ) : ℝ) - 1 - 2 * (l : ℝ)) hF
      (JacquetLimit.norm_modulusCharacter (m + 1)) hC y hy hκ
    refine h.trans (le_of_eq ?_)
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, hy, Real.one_rpow, one_mul]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    congr 1
    push_cast
    ring

variable {ι : Type*} [LinearOrder ι] {N : ℕ} {cl : Fin N → ι}

/-- `n̄(X)` as an element of `GL_N(ℝ)`. -/
def lowerCGL (hcl : Monotone cl) (X : CoordC cl → ℝ) : Langlands.GeneralLinear N ℝ :=
  (isUnit_lowerC hcl X).unit

theorem lowerCGL_val (hcl : Monotone cl) (X : CoordC cl → ℝ) :
    ((lowerCGL hcl X : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) = lowerC cl X :=
  IsUnit.unit_spec _

theorem gram_zero_lowerC (hcl : Monotone cl) (X : CoordC cl → ℝ) : gram 0 (lowerC cl X) = 1 := by
  rw [RealLeviTorus.gram_zero_eq, det_lowerC hcl, one_pow]

/-- `X ↦ ∏_l G_l(n̄(X))^{-1}` is integrable. -/
theorem integrable_prod_gram_inv (hcl : Monotone cl) :
    Integrable fun X : CoordC cl → ℝ =>
      ∏ l : Fin N, gram (l : ℕ) (lowerC cl X) ^ (-1 : ℝ) := by
  have hfin := gen N cl hcl (fun _ => -1) (fun _ _ => by norm_num) (fun _ _ _ _ => by norm_num)
  have hpos : ∀ X : CoordC cl → ℝ, 0 ≤ ∏ l : Fin N, gram (l : ℕ) (lowerC cl X) ^ (-1 : ℝ) :=
    fun X => Finset.prod_nonneg fun l _ => Real.rpow_nonneg (gram_lowerC_pos hcl X l).le _
  refine ⟨(continuous_prod_gram hcl (fun _ => -1)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hpos)]
  exact hfin

theorem continuous_lowerCGL_mul (hcl : Monotone cl) (κ : Langlands.GeneralLinear N ℝ) :
    Continuous fun X : CoordC cl → ℝ =>
      ((lowerCGL hcl X * κ : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) := by
  simp only [Units.val_mul, lowerCGL_val]
  exact continuous_lowerC.matrix_mul continuous_const

/-- **Integrability along `N̄`.** For smooth `F` with `F(diag(t) u g) = δ_B(t) F(g)` and
`κ ∈ O(N)`, `X ↦ F(n̄(X) κ)` is integrable, with the bound `C ∏_l G_l(n̄(X))^{-1}`. -/
theorem integrable_comp_lowerCGL {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hFs : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ F) (hF : IsModulusCovariant F)
    (hcl : Monotone cl) {κ : Langlands.GeneralLinear N ℝ} (hκ : κ ∈ unitaryCompact ℝ N) :
    Integrable fun X : CoordC cl → ℝ => F (lowerCGL hcl X * κ) := by
  obtain ⟨C, hC⟩ := exists_bound hFs
  refine ((integrable_prod_gram_inv hcl).const_mul C).mono'
    (continuous_comp_of_val hFs (continuous_lowerCGL_mul hcl κ)).aestronglyMeasurable
    (ae_of_all _ fun X => ?_)
  have h := norm_le_gram_inv hF hC (lowerCGL hcl X)
    (by rw [lowerCGL_val]; exact gram_zero_lowerC hcl X) hκ
  simpa only [lowerCGL_val] using h

end Growth

end RealLeviTwoBlock

end Langlands.Archimedean
