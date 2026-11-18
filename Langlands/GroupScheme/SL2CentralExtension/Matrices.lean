import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-! # Elementary matrices in `SL₂` over a commutative ring -/

open Matrix

namespace Langlands.GroupScheme.SL2CentralExtension.Mat

/-- Determinant-one `2 × 2` matrices. -/
abbrev SL2 (R : Type*) [CommRing R] := Matrix.SpecialLinearGroup (Fin 2) R

variable {R R' : Type*} [CommRing R] [CommRing R']

/-! ### Entries -/

theorem ext' {g g' : SL2 R} (h00 : g 0 0 = g' 0 0) (h01 : g 0 1 = g' 0 1)
    (h10 : g 1 0 = g' 1 0) (h11 : g 1 1 = g' 1 1) : g = g' := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

@[simp] theorem mul_00 (g g' : SL2 R) : (g * g') 0 0 = g 0 0 * g' 0 0 + g 0 1 * g' 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem mul_01 (g g' : SL2 R) : (g * g') 0 1 = g 0 0 * g' 0 1 + g 0 1 * g' 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem mul_10 (g g' : SL2 R) : (g * g') 1 0 = g 1 0 * g' 0 0 + g 1 1 * g' 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem mul_11 (g g' : SL2 R) : (g * g') 1 1 = g 1 0 * g' 0 1 + g 1 1 * g' 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem inv_00 (g : SL2 R) : g⁻¹ 0 0 = g 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] theorem inv_01 (g : SL2 R) : g⁻¹ 0 1 = -g 0 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] theorem inv_10 (g : SL2 R) : g⁻¹ 1 0 = -g 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] theorem inv_11 (g : SL2 R) : g⁻¹ 1 1 = g 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] theorem one_00 : (1 : SL2 R) 0 0 = 1 := by simp [Matrix.SpecialLinearGroup.coe_one]
@[simp] theorem one_01 : (1 : SL2 R) 0 1 = 0 := by simp [Matrix.SpecialLinearGroup.coe_one]
@[simp] theorem one_10 : (1 : SL2 R) 1 0 = 0 := by simp [Matrix.SpecialLinearGroup.coe_one]
@[simp] theorem one_11 : (1 : SL2 R) 1 1 = 1 := by simp [Matrix.SpecialLinearGroup.coe_one]

theorem det_eq (g : SL2 R) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.prop
  rw [Matrix.det_fin_two] at this
  exact this

@[simp] theorem map_apply' (f : R →+* R') (g : SL2 R) (i j : Fin 2) :
    Matrix.SpecialLinearGroup.map f g i j = f (g i j) := rfl

/-! ### The standard points -/

/-- The upper unipotent matrix `x(u)`. -/
def x (u : R) : SL2 R := ⟨!![1, u; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- The lower unipotent matrix `y(v)`. -/
def y (v : R) : SL2 R := ⟨!![1, 0; v, 1], by simp [Matrix.det_fin_two]⟩

/-- The diagonal matrix `h(t) = diag(t, t⁻¹)`. -/
def h (t : Rˣ) : SL2 R := ⟨!![(t : R), 0; 0, ((t⁻¹ : Rˣ) : R)], by simp [Matrix.det_fin_two]⟩

@[simp] theorem x_00 (u : R) : x u 0 0 = 1 := rfl
@[simp] theorem x_01 (u : R) : x u 0 1 = u := rfl
@[simp] theorem x_10 (u : R) : x u 1 0 = 0 := rfl
@[simp] theorem x_11 (u : R) : x u 1 1 = 1 := rfl
@[simp] theorem y_00 (v : R) : y v 0 0 = 1 := rfl
@[simp] theorem y_01 (v : R) : y v 0 1 = 0 := rfl
@[simp] theorem y_10 (v : R) : y v 1 0 = v := rfl
@[simp] theorem y_11 (v : R) : y v 1 1 = 1 := rfl
@[simp] theorem h_00 (t : Rˣ) : h t 0 0 = t := rfl
@[simp] theorem h_01 (t : Rˣ) : h t 0 1 = 0 := rfl
@[simp] theorem h_10 (t : Rˣ) : h t 1 0 = 0 := rfl
@[simp] theorem h_11 (t : Rˣ) : h t 1 1 = ((t⁻¹ : Rˣ) : R) := rfl

theorem x_add (u u' : R) : x (u + u') = x u * x u' := by
  apply ext' <;> simp
  ring

@[simp] theorem x_zero : x (0 : R) = 1 := by
  apply ext' <;> simp

theorem y_add (v v' : R) : y (v + v') = y v * y v' := by
  apply ext' <;> simp

@[simp] theorem y_zero : y (0 : R) = 1 := by
  apply ext' <;> simp

theorem h_mul (t t' : Rˣ) : h (t * t') = h t * h t' := by
  apply ext' <;> simp [mul_comm]

@[simp] theorem h_one : h (1 : Rˣ) = 1 := by
  apply ext' <;> simp

theorem x_neg (u : R) : x (-u) = (x u)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← x_add, neg_add_cancel, x_zero]

theorem y_neg (v : R) : y (-v) = (y v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← y_add, neg_add_cancel, y_zero]

theorem h_inv (t : Rˣ) : h t⁻¹ = (h t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← h_mul, inv_mul_cancel, h_one]

theorem h_comm (t t' : Rˣ) : h t * h t' = h t' * h t := by
  rw [← h_mul, ← h_mul, mul_comm]

theorem h_x (t : Rˣ) (u : R) : h t * x u = x (t * t * u) * h t := by
  have h1 : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  apply ext' <;> simp
  linear_combination (-(↑t * u)) * h1

theorem h_y (t : Rˣ) (v : R) :
    h t * y v = y (((t⁻¹ : Rˣ) : R) * ((t⁻¹ : Rˣ) : R) * v) * h t := by
  have h1 : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  apply ext' <;> simp
  linear_combination (-(↑t⁻¹ : R) * v) * h1

theorem map_x (f : R →+* R') (u : R) : Matrix.SpecialLinearGroup.map f (x u) = x (f u) := by
  apply ext' <;> simp

theorem map_y (f : R →+* R') (v : R) : Matrix.SpecialLinearGroup.map f (y v) = y (f v) := by
  apply ext' <;> simp

theorem map_h (f : R →+* R') (t : Rˣ) :
    Matrix.SpecialLinearGroup.map f (h t) = h (Units.map f.toMonoidHom t) := by
  apply ext' <;> simp

/-! ### Roots and their torus actions, uniformly for `x` and `y` -/

/-- The root group points: `x` for `false`, `y` for `true`. -/
def root : Bool → R → SL2 R
  | false, u => x u
  | true, v => y v

/-- The torus parameter acting on `root b` by the square character: `h(s)` acts on `x` by `s²`
and `h(s⁻¹)` acts on `y` by `s²`. -/
def lam : Bool → Rˣ → SL2 R
  | false, s => h s
  | true, s => h s⁻¹

theorem root_add (b : Bool) (u u' : R) : root b (u + u') = root b u * root b u' := by
  cases b
  · exact x_add u u'
  · exact y_add u u'

@[simp] theorem root_zero (b : Bool) : root b (0 : R) = 1 := by
  cases b
  · exact x_zero
  · exact y_zero

theorem root_neg (b : Bool) (u : R) : root b (-u) = (root b u)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← root_add, neg_add_cancel, root_zero]

theorem root_comm (b : Bool) (u u' : R) : root b u * root b u' = root b u' * root b u := by
  rw [← root_add, ← root_add, add_comm]

theorem lam_mul (b : Bool) (s s' : Rˣ) : lam b (s * s') = lam b s * lam b s' := by
  cases b
  · exact h_mul s s'
  · change h (s * s')⁻¹ = h s⁻¹ * h s'⁻¹
    rw [← h_mul, mul_inv, mul_comm]

theorem lam_eq_h (b : Bool) (s : Rˣ) : ∃ t : Rˣ, lam b s = h t := by
  cases b
  · exact ⟨s, rfl⟩
  · exact ⟨s⁻¹, rfl⟩

theorem lam_root (b : Bool) (s : Rˣ) (u : R) :
    lam b s * root b u = root b ((s : R) * s * u) * lam b s := by
  cases b
  · exact h_x s u
  · change h s⁻¹ * y u = y _ * h s⁻¹
    rw [h_y, inv_inv]

theorem lam_root_conj (b : Bool) (s : Rˣ) (u : R) :
    lam b s * root b u * (lam b s)⁻¹ = root b ((s : R) * s * u) := by
  rw [lam_root, mul_inv_cancel_right]

theorem lam_comm (b b' : Bool) (s s' : Rˣ) : lam b s * lam b' s' = lam b' s' * lam b s := by
  obtain ⟨t, ht⟩ := lam_eq_h b s
  obtain ⟨t', ht'⟩ := lam_eq_h b' s'
  rw [ht, ht', h_comm]

/-- The commutator of the torus with a root group. -/
theorem lam_root_commutator (b : Bool) (s : Rˣ) (u : R) :
    lam b s * root b u * (lam b s)⁻¹ * (root b u)⁻¹ = root b (((s : R) * s - 1) * u) := by
  rw [lam_root_conj, ← root_neg, ← root_add]
  congr 1
  ring

theorem map_root (f : R →+* R') (b : Bool) (u : R) :
    Matrix.SpecialLinearGroup.map f (root b u) = root b (f u) := by
  cases b
  · exact map_x f u
  · exact map_y f u

theorem map_lam (f : R →+* R') (b : Bool) (s : Rˣ) :
    Matrix.SpecialLinearGroup.map f (lam b s) = lam b (Units.map f.toMonoidHom s) := by
  cases b
  · exact map_h f s
  · change Matrix.SpecialLinearGroup.map f (h s⁻¹) = h (Units.map f.toMonoidHom s)⁻¹
    rw [map_h, map_inv]

/-! ### The Weyl element and the open cell -/

/-- Conrad's `g(t) = y(-1/t) x(t) y(-1/t) = [[0, t], [-1/t, 0]]`. -/
def w (t : Rˣ) : SL2 R := y (-((t⁻¹ : Rˣ) : R)) * x (t : R) * y (-((t⁻¹ : Rˣ) : R))

theorem w_00 (t : Rˣ) : w t 0 0 = 0 := by
  simp [w]

theorem w_01 (t : Rˣ) : w t 0 1 = t := by simp [w]

theorem w_10 (t : Rˣ) : w t 1 0 = -((t⁻¹ : Rˣ) : R) := by
  simp [w]

theorem w_11 (t : Rˣ) : w t 1 1 = 0 := by
  simp [w]

theorem w_mul_w_one_inv (t : Rˣ) : w t * (w 1)⁻¹ = h t := by
  apply ext' <;> simp [w_00, w_01, w_10, w_11]

theorem map_w (f : R →+* R') (t : Rˣ) :
    Matrix.SpecialLinearGroup.map f (w t) = w (Units.map f.toMonoidHom t) := by
  simp only [w, map_mul, map_y, map_x, map_neg]
  rfl

/-- The open cell: matrices with invertible upper-left entry. -/
def cell (g : SL2 R) : Prop := IsUnit (g 0 0)

/-- The product `y(a) h(t) x(b)`. -/
def yhx (a : R) (t : Rˣ) (b : R) : SL2 R := y a * h t * x b

@[simp] theorem yhx_00 (a : R) (t : Rˣ) (b : R) : yhx a t b 0 0 = t := by simp [yhx]
@[simp] theorem yhx_01 (a : R) (t : Rˣ) (b : R) : yhx a t b 0 1 = t * b := by simp [yhx]
@[simp] theorem yhx_10 (a : R) (t : Rˣ) (b : R) : yhx a t b 1 0 = a * t := by simp [yhx]

theorem cell_yhx (a : R) (t : Rˣ) (b : R) : cell (yhx a t b) := by
  rw [cell, yhx_00]
  exact t.isUnit

/-- The decomposition `y(a) h(t) x(b)` of a point of the open cell is unique. -/
theorem yhx_injective {a a' : R} {t t' : Rˣ} {b b' : R} (he : yhx a t b = yhx a' t' b') :
    a = a' ∧ t = t' ∧ b = b' := by
  have h00 := congrArg (fun g : SL2 R => g 0 0) he
  have h01 := congrArg (fun g : SL2 R => g 0 1) he
  have h10 := congrArg (fun g : SL2 R => g 1 0) he
  simp only [yhx_00, yhx_01, yhx_10] at h00 h01 h10
  have ht : t = t' := Units.ext h00
  subst ht
  refine ⟨?_, rfl, ?_⟩
  · have := congrArg (· * ((t⁻¹ : Rˣ) : R)) h10
    simpa [mul_assoc] using this
  · have := congrArg (((t⁻¹ : Rˣ) : R) * ·) h01
    simpa [← mul_assoc] using this

/-- Every point of the open cell is `y(g₁₀/g₀₀) h(g₀₀) x(g₀₁/g₀₀)`. -/
theorem eq_yhx (g : SL2 R) (t : Rˣ) (ht : (t : R) = g 0 0) :
    g = yhx (g 1 0 * ((t⁻¹ : Rˣ) : R)) t (((t⁻¹ : Rˣ) : R) * g 0 1) := by
  have h1 : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  have hdet := det_eq g
  apply ext'
  · simp [ht]
  · simp only [yhx_01]
    linear_combination (-g 0 1) * h1
  · simp only [yhx_10]
    linear_combination (-g 1 0) * h1
  · simp [yhx]
    rw [← ht] at hdet
    linear_combination (↑t⁻¹ : R) * hdet - g 1 1 * h1

theorem map_yhx (f : R →+* R') (a : R) (t : Rˣ) (b : R) :
    Matrix.SpecialLinearGroup.map f (yhx a t b) = yhx (f a) (Units.map f.toMonoidHom t) (f b) := by
  simp only [yhx, map_mul, map_y, map_h, map_x]

/-- The Bruhat-cell relation `x(u) y(v) = y(v/(1+uv)) h(1+uv) x(u/(1+uv))`. -/
theorem x_mul_y (u v : R) (s : Rˣ) (hs : (s : R) = 1 + u * v) :
    x u * y v = yhx (v * ((s⁻¹ : Rˣ) : R)) s (u * ((s⁻¹ : Rˣ) : R)) := by
  have h1 : (s : R) * ((s⁻¹ : Rˣ) : R) = 1 := Units.mul_inv s
  apply ext'
  · simp [hs]
  · simp only [yhx_01, mul_01, x_00, x_01, y_01, y_11]
    linear_combination (-u) * h1
  · simp only [yhx_10, mul_10, x_10, x_11, y_00, y_10]
    linear_combination (-v) * h1
  · simp [yhx]
    rw [hs] at h1
    linear_combination -h1

theorem x_mul_00 (r : R) (g : SL2 R) : (x r * g) 0 0 = g 0 0 + r * g 1 0 := by simp

/-- The first column of a determinant-one matrix is unimodular. -/
theorem col_unimodular (g : SL2 R) : g 1 1 * g 0 0 + (-g 0 1) * g 1 0 = 1 := by
  linear_combination det_eq g

/-- The first column of the inverse, `(g₁₁, -g₁₀)`, is unimodular. -/
theorem inv_col_unimodular (g : SL2 R) : g 0 0 * g 1 1 + g 0 1 * (-g 1 0) = 1 := by
  linear_combination det_eq g

end Langlands.GroupScheme.SL2CentralExtension.Mat
