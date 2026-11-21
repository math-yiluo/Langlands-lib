import Langlands.Group.GL.UpperBruhatCoordinatesProof
import Langlands.Representation.Archimedean.PrincipalSeriesExtension

/-! # Smooth triangular coordinates on the real trailing-minor chart -/

noncomputable section

open Set Matrix
open scoped Matrix.Norms.Operator ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GeneralLinear.RealBruhatTrailingChart

open UpperBruhatCoordinates

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GLₙ" => Langlands.GeneralLinear n ℝ

/-- The upper triangular part of a coordinate matrix, including the diagonal. -/
def upperProjection (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ({ toFun := fun x i j => if j < i then 0 else x i j
     map_add' := fun x y => by ext i j; by_cases h : j < i <;> simp [h]
     map_smul' := fun c x => by ext i j; by_cases h : j < i <;> simp [h] } :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ).toContinuousLinearMap

@[simp]
theorem upperProjection_apply (x : Mat) (i j : Fin n) :
    upperProjection n x i j = if j < i then 0 else x i j := rfl

private theorem isUpperTriangular_upperProjection (x : Mat) : (upperProjection n x).IsUpperTriangular :=
  fun i j hij => (upperProjection_apply x i j).trans (ite_eq_left (show j < i from hij))

/-- The lower unitriangular matrix encoded by the strict lower entries. -/
def lowerFactorOfCoordinates (x : Mat) : Mat := 1 + (x - upperProjection n x)

private def LowerShape (x : Mat) : Prop :=
  (∀ i j, i < j → x i j = 0) ∧ ∀ i, x i i = 1

private theorem lowerShape_lowerFactorOfCoordinates (x : Mat) :
    LowerShape (lowerFactorOfCoordinates x) := by
  constructor
  · intro i j hij
    simp [lowerFactorOfCoordinates, Matrix.one_apply_ne hij.ne, not_lt_of_ge hij.le]
  · intro i
    simp [lowerFactorOfCoordinates]

private theorem isUnit_of_lowerShape {x : Mat} (hx : LowerShape x) : IsUnit x := by
  have ht : x.transpose.IsUpperTriangular := fun i j hij => hx.1 j i hij
  rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.det_transpose, Matrix.det_of_isUpperTriangular ht]
  simp [hx.2]

private theorem lowerShape_inv {x : Mat} (hx : LowerShape x) : LowerShape x⁻¹ := by
  obtain ⟨u, rfl⟩ := isUnit_of_lowerShape hx
  have hu : u ∈ lowerUnipotent n ℝ := (mem_lowerUnipotent_iff _ _ u).mpr hx
  have h := (mem_lowerUnipotent_iff _ _ u⁻¹).mp ((lowerUnipotent n ℝ).inv_mem hu)
  simpa only [LowerShape, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit] using h

/-- The trailing square block of a real matrix. -/
def trailingBlock (c : Fin n) : Mat →L[ℝ] Matrix {k : Fin n // c < k} {k : Fin n // c < k} ℝ :=
  ({ toFun := fun y => y.toBlock (fun k => c < k) (fun k => c < k)
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
    Mat →ₗ[ℝ] Matrix {k : Fin n // c < k} {k : Fin n // c < k} ℝ).toContinuousLinearMap

/-- The open locus of invertible matrices with all trailing minors nonzero. -/
def trailingDomain (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {y | IsUnit y ∧ ∀ c : Fin n, (trailingBlock c y).det ≠ 0}

variable (n) in
theorem isOpen_trailingDomain : IsOpen (trailingDomain n) := by
  have h (c : Fin n) : IsOpen {y : Mat | (trailingBlock c y).det ≠ 0} :=
    isOpen_ne_fun ((trailingBlock c).continuous.matrix_det) continuous_const
  have he : trailingDomain n = {y : Mat | IsUnit y} ∩ ⋂ c : Fin n,
      {y | (trailingBlock c y).det ≠ 0} := by
    ext y
    simp [trailingDomain]
  rw [he]
  exact Langlands.Archimedean.isOpen_setOf_isUnit_matrix.inter (isOpen_iInter_of_finite h)

/-- The inverse lower factor, computed by clearing the strict lower entries. -/
def lowerSolve (y : Mat) : Mat := columnSolve (fun c k => c < k) y

private theorem lowerShape_lowerSolve (y : Mat) : LowerShape (lowerSolve y) := by
  constructor
  · intro i j hij
    rw [lowerSolve, columnSolve_apply_of_neg _ _ (not_lt_of_ge hij.le)]
    simp [hij.ne]
  · intro i
    rw [lowerSolve, columnSolve_apply_of_neg _ _ (lt_irrefl i)]
    simp

private theorem upper_triangular_mul_lowerSolve {y : Mat} (hy : y ∈ trailingDomain n) :
    (y * lowerSolve y).IsUpperTriangular := by
  intro i j hij
  exact mul_columnSolve_apply (fun c k => c < k) y (lt_irrefl j) (hy.2 j) hij

private theorem contDiffAt_nonsingularInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : Matrix ι ι ℝ} (hx : IsUnit x) : ContDiffAt ℝ ∞ (fun y : Matrix ι ι ℝ => y⁻¹) x := by
  obtain ⟨u, rfl⟩ := hx
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  exact contDiffAt_ringInverse ℝ u

private theorem contDiffOn_of_matrix_entries {s : Set Mat} {f : Mat → Mat}
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) : ContDiffOn ℝ ∞ f s := by
  let A : (Fin n → Fin n → ℝ) →L[ℝ] Mat :=
    ({ toFun := fun x => Matrix.of x
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : (Fin n → Fin n → ℝ) →ₗ[ℝ] Mat).toContinuousLinearMap
  exact A.contDiff.comp_contDiffOn (contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr (hf i))

theorem contDiffOn_lowerSolve : ContDiffOn ℝ ∞ (lowerSolve (n := n)) (trailingDomain n) := by
  apply contDiffOn_of_matrix_entries
  intro i j
  by_cases hij : j < i
  · simp only [lowerSolve, columnSolve_apply_of_pos _ _ hij, Matrix.mulVec, dotProduct]
    apply ContDiffOn.neg
    apply ContDiffOn.sum
    intro k _
    have hB : ContDiffOn ℝ ∞ (fun x : Mat => (trailingBlock j x)⁻¹) (trailingDomain n) := by
      intro x hx
      have hu : IsUnit (trailingBlock j x) :=
        (Matrix.isUnit_iff_isUnit_det (trailingBlock j x)).mpr (isUnit_iff_ne_zero.mpr (hx.2 j))
      exact ((contDiffAt_nonsingularInverse hu).comp x (trailingBlock j).contDiff.contDiffAt).contDiffWithinAt
    exact ((Matrix.entryLinearMap ℝ ℝ ⟨i, hij⟩ k).toContinuousLinearMap.contDiff.comp_contDiffOn hB).mul
      (Langlands.Archimedean.PrincipalSeriesExtension.contDiff_entry k.val j).contDiffOn
  · simp only [lowerSolve, columnSolve_apply_of_neg _ _ hij]
    exact contDiffOn_const

private theorem mem_trailingDomain_mul {b l : Mat}
    (hb : b.IsUpperTriangular) (hbU : IsUnit b) (hl : LowerShape l) : b * l ∈ trailingDomain n := by
  have hli := lowerShape_inv hl
  have hlU := isUnit_of_lowerShape hl
  refine ⟨hbU.mul hlU, fun c => ?_⟩
  obtain ⟨B, hB⟩ := hbU
  have hdiag : ∀ i, b i i ≠ 0 := by
    intro i
    have hb' : B.val.IsUpperTriangular := hB.symm ▸ hb
    simpa only [hB] using diag_ne_zero_of_upper B hb' i
  have hdet := det_toBlock_ne_zero_of_upper b hb hdiag (fun k => c < k)
  have hblock := toBlock_mul_of_support (fun k => c < k) (b * l) l⁻¹
    (fun k t hk ht => hli.1 k t (lt_of_le_of_lt (not_lt.mp hk) ht))
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det l).mp hlU), mul_one] at hblock
  rw [hblock, Matrix.det_mul] at hdet
  exact left_ne_zero_of_mul hdet

private theorem lowerSolve_mul {b l : Mat} (hb : b.IsUpperTriangular) (hbU : IsUnit b)
    (hl : LowerShape l) : lowerSolve (b * l) = l⁻¹ := by
  have hli := lowerShape_inv hl
  have hunit := (Matrix.isUnit_iff_isUnit_det l).mp (isUnit_of_lowerShape hl)
  symm
  refine eq_columnSolve (fun c k => c < k) (b * l) l⁻¹ (fun c => lt_irrefl c)
    (mem_trailingDomain_mul hb hbU hl).2 ?_ ?_
  · intro i j hij
    rcases eq_or_ne i j with rfl | hn
    · simp [hli.2]
    · rw [hli.1 i j ((not_lt.mp hij).lt_of_ne hn)]
      simp [hn]
  · intro i j hij
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, mul_one]
    exact hb hij

/-- The coordinate domain for the invertible upper factor. -/
def coordinateDomain (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) := {x | ∀ i : Fin n, x i i ≠ 0}

variable (n) in
theorem isOpen_coordinateDomain : IsOpen (coordinateDomain n) := by
  have he : coordinateDomain n = ⋂ i : Fin n, {x : Mat | x i i ≠ 0} := by
    ext x
    simp [coordinateDomain]
  rw [he]
  exact isOpen_iInter_of_finite fun i => isOpen_ne_fun
    (Langlands.Archimedean.PrincipalSeriesExtension.contDiff_entry i i).continuous continuous_const

/-- Multiply the upper factor by the lower unitriangular factor encoded by `x`. -/
def chartValue (x : Mat) : Mat := upperProjection n x * lowerFactorOfCoordinates x

/-- Recover both coordinate arrays after a lower column solve. -/
def inverseValue (y : Mat) : Mat := y * lowerSolve y + ((lowerSolve y)⁻¹ - 1)

private theorem isUnit_upperProjection {x : Mat} (hx : x ∈ coordinateDomain n) :
    IsUnit (upperProjection n x) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular (isUpperTriangular_upperProjection x),
    isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by simpa using hx i

private theorem upperProjection_inverseValue {y : Mat} (hy : y ∈ trailingDomain n) :
    upperProjection n (inverseValue y) = y * lowerSolve y := by
  let b := y * lowerSolve y
  have hb := upper_triangular_mul_lowerSolve hy
  have h := lowerShape_inv (lowerShape_lowerSolve y)
  ext i j
  by_cases hij : j < i
  · rw [upperProjection_apply, ite_eq_left hij, hb hij]
  · rw [upperProjection_apply, ite_eq_right hij]
    change b i j + ((lowerSolve y)⁻¹ i j - (1 : Mat) i j) = b i j
    by_cases hEq : i = j
    · subst j; simp [h.2]
    · rw [h.1 i j ((not_lt.mp hij).lt_of_ne hEq), Matrix.one_apply_ne hEq, sub_self, add_zero]

private theorem inverseValue_mem_coordinateDomain {y : Mat} (hy : y ∈ trailingDomain n) :
    inverseValue y ∈ coordinateDomain n := by
  have hu : IsUnit (y * lowerSolve y) := hy.1.mul (isUnit_of_lowerShape (lowerShape_lowerSolve y))
  obtain ⟨g, hg⟩ := hu
  have ht := upper_triangular_mul_lowerSolve hy
  intro i
  have h := diag_ne_zero_of_upper g (hg.symm ▸ ht) i
  rw [hg, ← upperProjection_inverseValue hy, upperProjection_apply, ite_eq_right (lt_irrefl i)] at h
  exact h

private theorem chartValue_inverseValue {y : Mat} (hy : y ∈ trailingDomain n) :
    chartValue (inverseValue y) = y := by
  rw [chartValue, lowerFactorOfCoordinates, upperProjection_inverseValue hy]
  have h : 1 + (inverseValue y - y * lowerSolve y) = (lowerSolve y)⁻¹ := by
    unfold inverseValue
    abel
  rw [h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det (lowerSolve y)).mp (isUnit_of_lowerShape (lowerShape_lowerSolve y))),
    mul_one]

private theorem inverseValue_chartValue {x : Mat} (hx : x ∈ coordinateDomain n) :
    inverseValue (chartValue x) = x := by
  have hl := lowerShape_lowerFactorOfCoordinates x
  have hunit := (Matrix.isUnit_iff_isUnit_det (lowerFactorOfCoordinates x)).mp (isUnit_of_lowerShape hl)
  have h := lowerSolve_mul (isUpperTriangular_upperProjection x) (isUnit_upperProjection hx) hl
  rw [inverseValue, chartValue, h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit,
    mul_one, Matrix.nonsing_inv_nonsing_inv _ hunit]
  unfold lowerFactorOfCoordinates
  abel

private theorem contDiff_chartValue : ContDiff ℝ ∞ (chartValue (n := n)) :=
  (upperProjection n).contDiff.mul (contDiff_const.add (contDiff_id.sub (upperProjection n).contDiff))

private theorem contDiffOn_inverseValue : ContDiffOn ℝ ∞ (inverseValue (n := n)) (trailingDomain n) := by
  refine (contDiffOn_id.mul contDiffOn_lowerSolve).add (ContDiffOn.sub ?_ contDiffOn_const)
  intro y hy
  have h : ContDiffAt ℝ ∞ (lowerSolve (n := n)) y :=
    contDiffOn_lowerSolve.contDiffAt ((isOpen_trailingDomain n).mem_nhds hy)
  exact ((contDiffAt_nonsingularInverse (isUnit_of_lowerShape (lowerShape_lowerSolve y))).comp y h).contDiffWithinAt

/-- Upper times lower unitriangular gives a smooth open matrix chart. -/
def trailingChart (n : ℕ) : OpenPartialHomeomorph (Matrix (Fin n) (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ) where
  toFun := chartValue
  invFun := inverseValue
  source := coordinateDomain n
  target := trailingDomain n
  map_source' x hx := mem_trailingDomain_mul (isUpperTriangular_upperProjection x)
    (isUnit_upperProjection hx) (lowerShape_lowerFactorOfCoordinates x)
  map_target' _ := inverseValue_mem_coordinateDomain
  left_inv' _ := inverseValue_chartValue
  right_inv' _ := chartValue_inverseValue
  open_source := isOpen_coordinateDomain n
  open_target := isOpen_trailingDomain n
  continuousOn_toFun := contDiff_chartValue.continuous.continuousOn
  continuousOn_invFun := contDiffOn_inverseValue.continuousOn

theorem contDiffOn_trailingChart (n : ℕ) :
    ContDiffOn ℝ ∞ (trailingChart n) (trailingChart n).source :=
  contDiff_chartValue.contDiffOn

theorem contDiffOn_trailingChart_symm (n : ℕ) :
    ContDiffOn ℝ ∞ (trailingChart n).symm (trailingChart n).target :=
  contDiffOn_inverseValue

/-- After removing its permutation on the right, each cell lies in the
trailing-minor chart. -/
theorem mem_trailingDomain_of_mem_cell (w : Equiv.Perm (Fin n)) {g : GLₙ}
    (hg : g ∈ upperBruhatCell n ℝ w) : (g * (permutation n ℝ w)⁻¹).val ∈ trailingDomain n := by
  obtain ⟨x, hx⟩ := upperBruhatCellMap_surjective w ⟨g, hg⟩
  have he := congrArg Subtype.val hx
  change (upperBruhatCellMap n ℝ w x).val = g at he
  refine ⟨(g * (permutation n ℝ w)⁻¹).isUnit, fun c => ?_⟩
  rw [← he]
  exact det_toBlock_recover_ne_zero w x c

private theorem inverseValue_lower_entry {y : Mat} (hy : y ∈ trailingDomain n)
    {i j : Fin n} (hij : j < i) : inverseValue y i j = (lowerSolve y)⁻¹ i j := by
  unfold inverseValue
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [upper_triangular_mul_lowerSolve hy hij, Matrix.one_apply_ne hij.ne', sub_zero, zero_add]

/-- In these coordinates a cell is cut out by exactly the strict lower
coordinates whose indices remain in strict lower order under the inverse permutation. -/
theorem mem_cell_iff_inverseValue_lower_zero (w : Equiv.Perm (Fin n)) (g : GLₙ)
    (hy : (g * (permutation n ℝ w)⁻¹).val ∈ trailingDomain n) :
    g ∈ upperBruhatCell n ℝ w ↔ ∀ i j : Fin n, j < i → w⁻¹ j < w⁻¹ i →
      inverseValue (g * (permutation n ℝ w)⁻¹).val i j = 0 := by
  let p := permutation n ℝ w
  let y := (g * p⁻¹).val
  constructor
  · intro hg i j hij hw
    obtain ⟨x, hx⟩ := upperBruhatCellMap_surjective w ⟨g, hg⟩
    have hc := recover_eq w x
    rw [hx] at hc
    have hlow : (lowerSolve y)⁻¹ = (p * x.2.val * p⁻¹).val := by
      change (p * x.2.val⁻¹ * p⁻¹).val = lowerSolve y at hc
      rw [← hc, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
      congr 1
      group
    rw [inverseValue_lower_entry hy hij, hlow, permutation_conjugate_entry]
    exact x.2.property.1.1 hw
  · intro hz
    let q : GLₙ := (isUnit_of_lowerShape (lowerShape_lowerSolve y)).unit
    have hq : q.val = lowerSolve y := IsUnit.unit_spec _
    have hqi : q⁻¹.val = (lowerSolve y)⁻¹ := by
      rw [← hq, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
    have hl : LowerShape q⁻¹.val := hqi ▸ lowerShape_inv (lowerShape_lowerSolve y)
    let v : GLₙ := p⁻¹ * q⁻¹ * p
    have hv (i j : Fin n) : v.val i j = q⁻¹.val (w i) (w j) := by
      have he := permutation_conjugate_entry n ℝ w⁻¹ q⁻¹ i j
      simpa only [← permutation_inv, inv_inv] using he
    have hvU : v ∈ upperUnipotent n ℝ := by
      refine ⟨fun i j hij => ?_, fun i => (hv i i).trans (hl.2 (w i))⟩
      rw [hv]
      rcases lt_or_gt_of_ne (fun h => hij.ne (w.injective h).symm) with h | h
      · exact hl.1 _ _ h
      · have hw : w⁻¹ (w j) < w⁻¹ (w i) := by simpa using hij
        have hh : w j < w i := h
        have he := hz (w i) (w j) hh hw
        rw [inverseValue_lower_entry hy hh, ← hqi] at he
        exact he
    let b : GLₙ := (g * p⁻¹) * q
    have hb : b ∈ upperTriangularSubgroup n ℝ := by
      change (y * q.val).IsUpperTriangular
      rw [hq]
      exact upper_triangular_mul_lowerSolve hy
    exact ⟨b, hb, v, hvU.1, by change g = b * p * v; dsimp only [b, v]; group⟩

/-- Smooth triangular coordinates contain each shifted Bruhat cell and
describe it by vanishing of the specified strict lower entries. -/
def RealBruhatTrailingChartStatement : Prop :=
  ∀ (n : ℕ),
    let e := trailingChart n
    ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ (w : Equiv.Perm (Fin n)) (g : Langlands.GeneralLinear n ℝ),
        let y := (g * (permutation n ℝ w)⁻¹).val
        (g ∈ upperBruhatCell n ℝ w → y ∈ e.target) ∧
        (y ∈ e.target → (g ∈ upperBruhatCell n ℝ w ↔
          ∀ i j : Fin n, j < i → w⁻¹ j < w⁻¹ i → e.symm y i j = 0))

theorem realBruhatTrailingChart : RealBruhatTrailingChartStatement :=
  fun n => ⟨contDiffOn_trailingChart n, contDiffOn_trailingChart_symm n, fun w g =>
    ⟨mem_trailingDomain_of_mem_cell w, mem_cell_iff_inverseValue_lower_zero w g⟩⟩

end Langlands.GeneralLinear.RealBruhatTrailingChart
