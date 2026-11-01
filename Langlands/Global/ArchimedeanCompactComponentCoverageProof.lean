import Langlands.Global.ArchimedeanCompactComponentCoverageStatement
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Compact representatives of archimedean connected components: proof -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open NumberField NumberField.InfinitePlace Matrix

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]
  {X : Type*} [TopologicalSpace X]

/-- A matrix-valued map with nonzero determinants, viewed in the general linear group. -/
def unitOfDetNeZero (F : X → Matrix m m 𝕜) (hF : ∀ x, (F x).det ≠ 0) (x : X) :
    Matrix.GeneralLinearGroup m 𝕜 :=
  ((Matrix.isUnit_iff_isUnit_det (F x)).mpr (hF x).isUnit).unit

omit [TopologicalSpace X] in
@[simp]
theorem val_unitOfDetNeZero (F : X → Matrix m m 𝕜) (hF : ∀ x, (F x).det ≠ 0) (x : X) :
    (unitOfDetNeZero F hF x : Matrix m m 𝕜) = F x := rfl

/-- A continuous matrix-valued map with nonzero determinants is continuous into the unit
group: its inverse is the inverse determinant times the adjugate. -/
theorem continuous_unitOfDetNeZero (F : X → Matrix m m 𝕜) (hF : ∀ x, (F x).det ≠ 0)
    (hc : Continuous F) : Continuous (unitOfDetNeZero F hF) := by
  rw [Units.continuous_iff]
  refine ⟨hc, ?_⟩
  have hinv : (fun x => ((unitOfDetNeZero F hF x)⁻¹ : Matrix.GeneralLinearGroup m 𝕜).val) =
      fun x => (F x).det⁻¹ • (F x).adjugate := by
    funext x
    rw [Matrix.coe_units_inv, val_unitOfDetNeZero, Matrix.inv_def, Ring.inverse_eq_inv]
  rw [hinv]
  exact (hc.matrix_det.inv₀ hF).smul hc.matrix_adjugate

/-- The transvection with its off-diagonal entry multiplied by `s`. -/
def scaleTransvection (s : 𝕜) (T : TransvectionStruct m 𝕜) : TransvectionStruct m 𝕜 :=
  ⟨T.i, T.j, T.hij, s * T.c⟩

omit [Fintype m] [DecidableEq m] in
theorem scaleTransvection_one (T : TransvectionStruct m 𝕜) : scaleTransvection 1 T = T := by
  cases T
  simp [scaleTransvection]

omit [Fintype m] in
theorem toMatrix_scaleTransvection_zero (T : TransvectionStruct m 𝕜) :
    (scaleTransvection 0 T).toMatrix = 1 := by
  simp [scaleTransvection, TransvectionStruct.toMatrix]

omit [Fintype m] in
theorem continuous_toMatrix_scaleTransvection (T : TransvectionStruct m 𝕜) :
    Continuous fun s : ℝ => (scaleTransvection (s : 𝕜) T).toMatrix := by
  refine continuous_matrix fun a b => ?_
  simp only [scaleTransvection, TransvectionStruct.toMatrix, transvection, Matrix.add_apply,
    Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> fun_prop

theorem det_prod_scaleTransvection (s : 𝕜) (L : List (TransvectionStruct m 𝕜)) :
    (L.map fun T => (scaleTransvection s T).toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons T L ih => simp [ih]

theorem continuous_prod_scaleTransvection (L : List (TransvectionStruct m 𝕜)) :
    Continuous fun s : ℝ => (L.map fun T => (scaleTransvection (s : 𝕜) T).toMatrix).prod :=
  continuous_list_prod L fun T _ => continuous_toMatrix_scaleTransvection T

theorem prod_scaleTransvection_zero (L : List (TransvectionStruct m 𝕜)) :
    (L.map fun T => (scaleTransvection ((0 : ℝ) : 𝕜) T).toMatrix).prod = 1 := by
  simp [toMatrix_scaleTransvection_zero]

/-- The diagonal unitary matrix with entries `d i / ‖d i‖`. -/
theorem diagonal_normalize_mem_unitaryGroup (d : m → 𝕜) (hd : ∀ i, d i ≠ 0) :
    diagonal (fun i => d i * ((‖d i‖⁻¹ : ℝ) : 𝕜)) ∈ Matrix.unitaryGroup m 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have hn : (‖d i‖ : 𝕜) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr (hd i))
  simp only [Pi.star_apply, RCLike.star_def, map_mul, RCLike.conj_ofReal]
  calc (starRingEnd 𝕜) (d i) * ((‖d i‖⁻¹ : ℝ) : 𝕜) * (d i * ((‖d i‖⁻¹ : ℝ) : 𝕜))
      = ((starRingEnd 𝕜) (d i) * d i) * (((‖d i‖⁻¹ : ℝ) : 𝕜) * ((‖d i‖⁻¹ : ℝ) : 𝕜)) := by
        ring
    _ = 1 := by
        rw [RCLike.conj_mul]
        push_cast
        field_simp

/-- Every invertible real or complex matrix lies in the connected component of a unitary
matrix in the general linear group. -/
theorem exists_unitary_mem_connectedComponent (A : Matrix.GeneralLinearGroup m 𝕜) :
    ∃ U : Matrix.GeneralLinearGroup m 𝕜, (U : Matrix m m 𝕜) ∈ Matrix.unitaryGroup m 𝕜 ∧
      A ∈ connectedComponent U := by
  obtain ⟨L, L', D, hA⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (A : Matrix m m 𝕜)
  have hdetA : (A : Matrix m m 𝕜).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  have hD : ∀ i, D i ≠ 0 := by
    rw [hA] at hdetA
    simp only [det_mul, TransvectionStruct.det_toMatrix_prod, one_mul, mul_one,
      det_diagonal] at hdetA
    exact fun i => Finset.prod_ne_zero_iff.mp hdetA i (Finset.mem_univ i)
  -- The positive scaling factor at parameter `s`, equal to `1` at `s = 1`.
  let r : m → ℝ → ℝ := fun i s => Real.exp ((s - 1) * Real.log ‖D i‖)
  have hr : ∀ i s, r i s ≠ 0 := fun i s => (Real.exp_pos _).ne'
  let F : ℝ → Matrix m m 𝕜 := fun s =>
    (L.map fun T => (scaleTransvection (s : 𝕜) T).toMatrix).prod *
      diagonal (fun i => D i * ((r i s : ℝ) : 𝕜)) *
      (L'.map fun T => (scaleTransvection (s : 𝕜) T).toMatrix).prod
  have hF : ∀ s, (F s).det ≠ 0 := by
    intro s
    simp only [F, det_mul, det_prod_scaleTransvection, one_mul, mul_one, det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      mul_ne_zero (hD i) (RCLike.ofReal_ne_zero.mpr (hr i s))
  have hFc : Continuous F := by
    refine ((continuous_prod_scaleTransvection L).mul ?_).mul
      (continuous_prod_scaleTransvection L')
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fun_prop
  have hF1 : F 1 = (A : Matrix m m 𝕜) := by
    simp only [F, r, RCLike.ofReal_one, scaleTransvection_one, sub_self, zero_mul,
      Real.exp_zero, mul_one]
    exact hA.symm
  have hF0 : F 0 = diagonal (fun i => D i * ((‖D i‖⁻¹ : ℝ) : 𝕜)) := by
    simp only [F, prod_scaleTransvection_zero, one_mul, mul_one, r]
    congr 1
    funext i
    rw [zero_sub, neg_one_mul, Real.exp_neg, Real.exp_log (norm_pos_iff.mpr (hD i))]
  let γ := unitOfDetNeZero F hF
  have hγ : Continuous γ := continuous_unitOfDetNeZero F hF hFc
  refine ⟨γ 0, ?_, ?_⟩
  · change F 0 ∈ Matrix.unitaryGroup m 𝕜
    rw [hF0]
    exact diagonal_normalize_mem_unitaryGroup D hD
  · have hA1 : A = γ 1 := Units.ext hF1.symm
    rw [hA1]
    exact (isConnected_range hγ).isPreconnected.subset_connectedComponent
      ⟨0, rfl⟩ ⟨1, rfl⟩

end RCLike

section Assemble

variable (K : Type u) [Field K] (n : ℕ)

/-- Per-place invertible matrices, real places and complex places separately. -/
abbrev PlaceGL :=
  ({v : InfinitePlace K // IsReal v} → Matrix.GeneralLinearGroup (Fin n) ℝ) ×
    ({v : InfinitePlace K // IsComplex v} → Matrix.GeneralLinearGroup (Fin n) ℂ)

/-- The matrix in mixed coordinates with prescribed real and complex place matrices. -/
def assembleMatrix
    (a : {v : InfinitePlace K // IsReal v} → Matrix (Fin n) (Fin n) ℝ)
    (b : {v : InfinitePlace K // IsComplex v} → Matrix (Fin n) (Fin n) ℂ) :
    ArchimedeanMatrix K n :=
  fun i j => (fun v => a v i j, fun v => b v i j)

theorem assembleMatrix_mul
    (a a' : {v : InfinitePlace K // IsReal v} → Matrix (Fin n) (Fin n) ℝ)
    (b b' : {v : InfinitePlace K // IsComplex v} → Matrix (Fin n) (Fin n) ℂ) :
    assembleMatrix K n a b * assembleMatrix K n a' b' =
      assembleMatrix K n (fun v => a v * a' v) (fun v => b v * b' v) := by
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · funext v
    change (RingHom.fst _ _) (∑ k, assembleMatrix K n a b i k * assembleMatrix K n a' b' k j) v
      = _
    rw [map_sum, Finset.sum_apply]
    rfl
  · funext v
    change (RingHom.snd _ _) (∑ k, assembleMatrix K n a b i k * assembleMatrix K n a' b' k j) v
      = _
    rw [map_sum, Finset.sum_apply]
    rfl

theorem assembleMatrix_one :
    assembleMatrix K n (fun _ => 1) (fun _ => 1) = 1 := by
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · funext v
    simp only [assembleMatrix, Matrix.one_apply]
    split_ifs <;> rfl
  · funext v
    simp only [assembleMatrix, Matrix.one_apply]
    split_ifs <;> rfl

/-- Assemble per-place invertible matrices, together with their inverses, in mixed
coordinates. -/
def assemble (y : PlaceGL K n) : ArchimedeanGL K n where
  val := assembleMatrix K n (fun v => (y.1 v : Matrix (Fin n) (Fin n) ℝ))
    (fun v => (y.2 v : Matrix (Fin n) (Fin n) ℂ))
  inv := assembleMatrix K n (fun v => ((y.1 v)⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℝ).val)
    (fun v => ((y.2 v)⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ).val)
  val_inv := by
    rw [assembleMatrix_mul]
    simp only [Units.mul_inv]
    exact assembleMatrix_one K n
  inv_val := by
    rw [assembleMatrix_mul]
    simp only [Units.inv_mul]
    exact assembleMatrix_one K n

theorem continuous_assemble : Continuous (assemble K n) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => Continuous.prodMk ?_ ?_
    · refine continuous_pi fun v => ?_
      have hv : Continuous fun y : PlaceGL K n => ((y.1 v : Matrix.GeneralLinearGroup (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) :=
        Units.continuous_val.comp ((continuous_apply v).comp continuous_fst)
      exact (continuous_apply j).comp ((continuous_apply i).comp hv)
    · refine continuous_pi fun v => ?_
      have hv : Continuous fun y : PlaceGL K n => ((y.2 v : Matrix.GeneralLinearGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ) :=
        Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)
      exact (continuous_apply j).comp ((continuous_apply i).comp hv)
  · refine continuous_pi fun i => continuous_pi fun j => Continuous.prodMk ?_ ?_
    · refine continuous_pi fun v => ?_
      have hv : Continuous fun y : PlaceGL K n =>
          (((y.1 v)⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) :=
        Units.continuous_coe_inv.comp ((continuous_apply v).comp continuous_fst)
      exact (continuous_apply j).comp ((continuous_apply i).comp hv)
    · refine continuous_pi fun v => ?_
      have hv : Continuous fun y : PlaceGL K n =>
          (((y.2 v)⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
        Units.continuous_coe_inv.comp ((continuous_apply v).comp continuous_snd)
      exact (continuous_apply j).comp ((continuous_apply i).comp hv)

/-- The per-place invertible matrices of a point of the mixed-coordinate group. -/
def places (g : ArchimedeanGL K n) : PlaceGL K n :=
  (fun v => Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun _ : {v : InfinitePlace K // IsReal v} => ℝ) v).comp
        (RingHom.fst _ _)) g,
    fun v => Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun _ : {v : InfinitePlace K // IsComplex v} => ℂ) v).comp
        (RingHom.snd _ _)) g)

theorem assemble_places (g : ArchimedeanGL K n) : assemble K n (places K n g) = g := by
  apply Units.ext
  rfl

/-- Every point of the mixed-coordinate group lies in the connected component of a point
assembled from orthogonal and unitary matrices. -/
theorem exists_compactFactors_mem_connectedComponent (g : ArchimedeanGL K n) :
    ∃ p : ArchimedeanCompactFactors K n,
      g ∈ connectedComponent (ArchimedeanCompactFactors.toArchimedeanGL K n p) := by
  choose uR huR hgR using fun v => exists_unitary_mem_connectedComponent ((places K n g).1 v)
  choose uC huC hgC using fun v => exists_unitary_mem_connectedComponent ((places K n g).2 v)
  refine ⟨(fun v => ⟨uR v, huR v⟩, fun v => ⟨uC v, huC v⟩), ?_⟩
  have hmem : places K n g ∈ connectedComponent ((uR, uC) : PlaceGL K n) := by
    rw [connectedComponent_prod, connectedComponent_pi, connectedComponent_pi]
    exact ⟨fun v _ => hgR v, fun v _ => hgC v⟩
  have himage := (continuous_assemble K n).image_connectedComponent_subset
    ((uR, uC) : PlaceGL K n) ⟨places K n g, hmem, assemble_places K n g⟩
  have hu : assemble K n ((uR, uC) : PlaceGL K n) =
      ArchimedeanCompactFactors.toArchimedeanGL K n
        (fun v => ⟨uR v, huR v⟩, fun v => ⟨uC v, huC v⟩) := by
    apply Units.ext
    rfl
  rwa [hu] at himage

end Assemble

/-- **Component coverage.** Every point of the actual archimedean general linear group lies
in the connected component of a point of the standard orthogonal/unitary compact
subgroup. -/
theorem compactComponentCoverage (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    CompactComponentCoverageStatement K n := by
  intro g
  obtain ⟨p, hp⟩ := exists_compactFactors_mem_connectedComponent K n
    (archimedeanGLCoordinates K n g)
  refine ⟨⟨ArchimedeanCompactFactors.toInfiniteAdelicGL K n p, p, rfl⟩, ?_⟩
  have h := (archimedeanGLCoordinates K n).symm.continuous.image_connectedComponent_subset
    (ArchimedeanCompactFactors.toArchimedeanGL K n p)
    ⟨archimedeanGLCoordinates K n g, hp, (archimedeanGLCoordinates K n).symm_apply_apply g⟩
  exact h

end Langlands.Global.ArchimedeanGL
