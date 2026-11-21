import Langlands.GroupScheme.Composition.CayleyIdentities
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fin.VecNotation

/-! # Orthogonal frames of Cayley algebras -/

noncomputable section

universe u

open Module LinearMap Matrix

namespace Langlands.GroupScheme.CayleyDatum

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

variable {K : Type u} [Field K] (c : CayleyDatum K)

local notation "V" => CayleyVector K
local notation "μ" => c.multiplication

/-- The multiplicative norm has nondegenerate polar form on both sides. -/
theorem norm_nondegenerate : c.form.Nondegenerate :=
  ⟨c.polar_nondegenerate, fun y h => c.polar_nondegenerate y fun x => (c.form_comm y x).trans (h x)⟩

/-- Left multiplication by a trace-zero vector is skew-adjoint for the norm pairing. -/
theorem form_mul_left_of_trace_zero {x : V} (hx : c.trace x = 0) (y z : V) :
    c.form (μ x y) z = -c.form y (μ x z) := by
  apply eq_neg_of_add_eq_zero_left
  simpa only [hx, zero_mul] using c.form_mul_left x y z

/-- The square of left multiplication by a trace-zero vector is scalar. -/
theorem mul_mul_left_of_trace_zero {x : V} (hx : c.trace x = 0) (z : V) :
    μ x (μ x z) = -(c.norm x • z) := by
  have h := c.mul_mul_left x z
  rw [hx, zero_smul, zero_sub] at h
  exact neg_eq_iff_eq_neg.mp h

/-- Left multiplications by orthogonal trace-zero vectors anticommute. -/
theorem mul_mul_left_anticommute {x y : V} (hx : c.trace x = 0) (hy : c.trace y = 0)
    (hxy : c.form x y = 0) (z : V) : μ x (μ y z) = -μ y (μ x z) := by
  have h := c.mul_mul_left₂ x y z
  simp only [hx, hy, hxy, zero_smul, zero_sub] at h
  apply eq_neg_of_add_eq_zero_left
  simpa only [neg_add, neg_neg, neg_zero] using congrArg Neg.neg h

private theorem form_self_mul_left_of_trace_zero (h2 : (2 : K) ≠ 0)
    {x : V} (hx : c.trace x = 0) (y : V) : c.form y (μ x y) = 0 := by
  have h := c.form_mul_left x y y
  rw [hx, zero_mul, c.form_comm (μ x y), ← two_mul] at h
  exact (mul_eq_zero.mp h).resolve_left h2

/-- Four vectors obtained by applying two orthogonal trace-zero generators on the left. -/
def leftFrameBlock (x y w : V) : Fin 4 → V := ![w, μ x w, μ y w, μ x (μ y w)]

/-- A frame block is orthogonal in characteristic different from two. -/
theorem orthogonal_leftFrameBlock (h2 : (2 : K) ≠ 0) {x y : V}
    (hx : c.trace x = 0) (hy : c.trace y = 0) (hxy : c.form x y = 0) (w : V) :
    c.form.iIsOrtho (c.leftFrameBlock x y w) := by
  have h01 := c.form_self_mul_left_of_trace_zero h2 hx w
  have h02 := c.form_self_mul_left_of_trace_zero h2 hy w
  have h12 : c.form (μ x w) (μ y w) = 0 := by rw [c.form_mul_mul_right, hxy, mul_zero]
  have h03 : c.form w (μ x (μ y w)) = 0 := by
    have h := c.form_mul_left x w (μ y w)
    rw [hx, zero_mul, h12, zero_add] at h
    exact h
  have h13 : c.form (μ x w) (μ x (μ y w)) = 0 := by rw [c.form_mul_mul_left, h02, mul_zero]
  have h23 := c.form_self_mul_left_of_trace_zero h2 hx (μ y w)
  apply LinearMap.BilinForm.iIsOrtho_def.mpr
  suffices h : ∀ i j : Fin 4, i < j → c.form (c.leftFrameBlock x y w i) (c.leftFrameBlock x y w j) = 0 by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact h i j hij
    · exact (c.form_comm _ _).trans (h j i hji)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [leftFrameBlock]

/-- All norms of one frame block are the corresponding norms of its unit block
multiplied by the norm of its starting vector. -/
theorem norm_leftFrameBlock (x y w : V) (i : Fin 4) :
    c.norm (c.leftFrameBlock x y w i) =
      c.norm (c.leftFrameBlock x y c.unit i) * c.norm w := by
  fin_cases i <;> simp [leftFrameBlock, c.norm_mul, c.norm_unit, c.mul_unit, mul_assoc]

/-- The four coefficients and indices of left multiplication by the first generator. -/
def leftFrameActionX (a : K) : Fin 4 → K × Fin 4 := ![(1, 1), (-a, 0), (1, 3), (-a, 2)]

/-- The four coefficients and indices of left multiplication by the second generator. -/
def leftFrameActionY (a : K) : Fin 4 → K × Fin 4 := ![(1, 2), (-1, 3), (-a, 0), (a, 1)]

/-- The action of the first generator is independent of the block's starting vector. -/
theorem mul_leftFrameBlock_x {x : V} (hx : c.trace x = 0) (y w : V) (i : Fin 4) :
    μ x (c.leftFrameBlock x y w i) = (leftFrameActionX (c.norm x) i).1 •
      c.leftFrameBlock x y w (leftFrameActionX (c.norm x) i).2 := by
  fin_cases i <;> simp [leftFrameBlock, leftFrameActionX, c.mul_mul_left_of_trace_zero hx, neg_smul]

/-- The action of the second generator is independent of the block's starting vector. -/
theorem mul_leftFrameBlock_y {x y : V} (hx : c.trace x = 0) (hy : c.trace y = 0)
    (hxy : c.form x y = 0) (w : V) (i : Fin 4) :
    μ y (c.leftFrameBlock x y w i) = (leftFrameActionY (c.norm y) i).1 •
      c.leftFrameBlock x y w (leftFrameActionY (c.norm y) i).2 := by
  have hyx : c.form y x = 0 := (c.form_comm _ _).trans hxy
  fin_cases i <;> simp [leftFrameBlock, leftFrameActionY, c.mul_mul_left_anticommute hy hx hyx,
    c.mul_mul_left_of_trace_zero hy, neg_smul]

/-- The parity signs of the words in the first two left multiplications. -/
def leftFrameSign : Fin 4 → K := ![1, -1, -1, 1]

/-- A pure vector orthogonal to both generators can be moved through either block
by the appropriate sign. -/
theorem mul_leftFrameBlock_of_orthogonal {x y z : V} (hx : c.trace x = 0) (hy : c.trace y = 0)
    (hz : c.trace z = 0) (hzx : c.form z x = 0) (hzy : c.form z y = 0) (w : V) (i : Fin 4) :
    μ z (c.leftFrameBlock x y w i) = leftFrameSign (K := K) i • c.leftFrameBlock x y (μ z w) i := by
  fin_cases i <;> simp [leftFrameBlock, leftFrameSign, c.mul_mul_left_anticommute hz hx hzx,
    c.mul_mul_left_anticommute hz hy hzy]

/-- Scaling the starting vector scales every member of the frame block. -/
theorem leftFrameBlock_smul (x y w : V) (a : K) (i : Fin 4) :
    c.leftFrameBlock x y (a • w) i = a • c.leftFrameBlock x y w i := by
  fin_cases i <;> simp [leftFrameBlock]

/-- The unit block and a block starting from a vector in its orthogonal complement. -/
def leftFrame (x y z : V) : Fin 4 ⊕ Fin 4 → V :=
  Sum.elim (c.leftFrameBlock x y c.unit) (c.leftFrameBlock x y z)

/-- Orthogonality of the two blocks of the Cayley frame. -/
theorem form_leftFrameBlock_cross {x y z : V} (hx : c.trace x = 0) (hy : c.trace y = 0)
    (hxy : c.form x y = 0) (hz : ∀ i, c.form (c.leftFrameBlock x y c.unit i) z = 0)
    (i j : Fin 4) : c.form (c.leftFrameBlock x y c.unit i) (c.leftFrameBlock x y z j) = 0 := by
  let A := c.leftFrameBlock x y c.unit
  have h (w : V) (hw : ∀ i, c.form (A i) w = 0) (i : Fin 4) :
      c.form (A i) (μ x w) = 0 ∧ c.form (A i) (μ y w) = 0 := by
    constructor
    · rw [c.form_comm, c.form_mul_left_of_trace_zero hx, show A i = _ from rfl,
        c.mul_leftFrameBlock_x hx, map_smul, c.form_comm w]
      change -((leftFrameActionX (c.norm x) i).1 • c.form (A (leftFrameActionX (c.norm x) i).2) w) = 0
      rw [hw, smul_zero, neg_zero]
    · rw [c.form_comm, c.form_mul_left_of_trace_zero hy, show A i = _ from rfl,
        c.mul_leftFrameBlock_y hx hy hxy, map_smul, c.form_comm w]
      change -((leftFrameActionY (c.norm y) i).1 • c.form (A (leftFrameActionY (c.norm y) i).2) w) = 0
      rw [hw, smul_zero, neg_zero]
  fin_cases j
  · exact hz i
  · exact (h z hz i).1
  · exact (h z hz i).2
  · exact (h (μ y z) (fun i => (h z hz i).2) i).1

/-- The eight frame vectors form a basis when the three generator norms are nonzero. -/
def leftFrameBasis (h2 : (2 : K) ≠ 0) {x y z : V} (hx : c.trace x = 0) (hy : c.trace y = 0)
    (hxy : c.form x y = 0) (hz : ∀ i, c.form (c.leftFrameBlock x y c.unit i) z = 0)
    (hNx : c.norm x ≠ 0) (hNy : c.norm y ≠ 0) (hNz : c.norm z ≠ 0) :
    Basis (Fin 4 ⊕ Fin 4) K V := by
  apply basisOfLinearIndependentOfCardEqFinrank (b := c.leftFrame x y z)
  · apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := c.form)
    · intro i j hij
      rcases i with i | i <;> rcases j with j | j
      · exact c.orthogonal_leftFrameBlock h2 hx hy hxy c.unit (fun h => hij (congrArg Sum.inl h))
      · exact c.form_leftFrameBlock_cross hx hy hxy hz i j
      · exact (c.form_comm _ _).trans (c.form_leftFrameBlock_cross hx hy hxy hz j i)
      · exact c.orthogonal_leftFrameBlock h2 hx hy hxy z (fun h => hij (congrArg Sum.inr h))
    · intro i
      have h (i : Fin 4) : c.norm (c.leftFrameBlock x y c.unit i) ≠ 0 := by
        fin_cases i <;> simp [leftFrameBlock, c.norm_unit, c.norm_mul, c.mul_unit, hNx, hNy]
      rw [c.form_self]
      apply mul_ne_zero h2
      rcases i with i | i
      · exact h i
      · change c.norm (c.leftFrameBlock x y z i) ≠ 0
        rw [c.norm_leftFrameBlock]
        exact mul_ne_zero (h i) hNz
  · simp [CayleyVector]

@[simp] theorem leftFrameBasis_apply (h2 : (2 : K) ≠ 0) {x y z : V} (hx : c.trace x = 0)
    (hy : c.trace y = 0) (hxy : c.form x y = 0) (hz : ∀ i, c.form (c.leftFrameBlock x y c.unit i) z = 0)
    (hNx : c.norm x ≠ 0) (hNy : c.norm y ≠ 0) (hNz : c.norm z ≠ 0) (i : Fin 4 ⊕ Fin 4) :
    c.leftFrameBasis h2 hx hy hxy hz hNx hNy hNz i = c.leftFrame x y z i := by
  unfold leftFrameBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

end Langlands.GroupScheme.CayleyDatum
