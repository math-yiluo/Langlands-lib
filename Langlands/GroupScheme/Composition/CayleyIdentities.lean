import Langlands.GroupScheme.Composition.CayleyDatum

/-! # Linearized composition identities of a Cayley datum -/

noncomputable section

universe u

namespace Langlands.GroupScheme.CayleyDatum

variable {K : Type u} [Field K] (c : CayleyDatum K)

/-- The polar bilinear form `b(x, y) = N(x + y) - N(x) - N(y)` of the norm. -/
abbrev form : LinearMap.BilinForm K (CayleyVector K) := c.norm.polarBilin

/-- The trace `T(x) = b(x, 1)`. -/
def trace (x : CayleyVector K) : K := c.form x c.unit

local notation "μ" => c.multiplication

theorem form_apply (x y : CayleyVector K) :
    c.form x y = c.norm (x + y) - c.norm x - c.norm y := rfl

theorem norm_add (x y : CayleyVector K) :
    c.norm (x + y) = c.norm x + c.norm y + c.form x y := by
  rw [form_apply]
  ring

theorem form_comm (x y : CayleyVector K) : c.form x y = c.form y x :=
  QuadraticMap.polar_comm _ x y

theorem form_self (x : CayleyVector K) : c.form x x = 2 * c.norm x := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul, two_mul]

theorem trace_unit : c.trace c.unit = 2 := by
  rw [trace, form_self, norm_unit, mul_one]

theorem trace_add (x y : CayleyVector K) : c.trace (x + y) = c.trace x + c.trace y := by
  simp [trace]

theorem trace_smul (a : K) (x : CayleyVector K) : c.trace (a • x) = a * c.trace x := by
  simp [trace]

theorem trace_sub (x y : CayleyVector K) : c.trace (x - y) = c.trace x - c.trace y := by
  simp [trace]

/-- Vectors with the same pairings against every vector are equal. -/
theorem eq_of_forall_form_eq {x y : CayleyVector K} (h : ∀ w, c.form w x = c.form w y) :
    x = y := by
  have h0 : x - y = 0 := by
    apply c.polar_nondegenerate
    intro w
    have := h w
    rw [map_sub, LinearMap.sub_apply]
    change c.form x w - c.form y w = 0
    rw [c.form_comm x, c.form_comm y, this, sub_self]
  exact sub_eq_zero.mp h0

/-- A vector orthogonal to every vector is zero. -/
theorem eq_zero_of_forall_form_eq_zero {x : CayleyVector K} (h : ∀ w, c.form w x = 0) :
    x = 0 :=
  c.eq_of_forall_form_eq fun w => by rw [h w, map_zero]

/-- **(I1)** `b(xy, xz) = N(x) b(y, z)`. -/
theorem form_mul_mul_left (x y z : CayleyVector K) :
    c.form (μ x y) (μ x z) = c.norm x * c.form y z := by
  have h := c.norm_mul x (y + z)
  rw [map_add, norm_add, norm_add, c.norm_mul, c.norm_mul] at h
  linear_combination h

/-- **(I1')** `b(yx, zx) = N(x) b(y, z)`. -/
theorem form_mul_mul_right (x y z : CayleyVector K) :
    c.form (μ y x) (μ z x) = c.norm x * c.form y z := by
  have h := c.norm_mul (y + z) x
  rw [map_add, LinearMap.add_apply, norm_add, norm_add, c.norm_mul, c.norm_mul] at h
  linear_combination h

/-- **(I2)** `b(xy, wz) + b(wy, xz) = b(x, w) b(y, z)`. -/
theorem form_mul_mul_left₂ (x w y z : CayleyVector K) :
    c.form (μ x y) (μ w z) + c.form (μ w y) (μ x z) = c.form x w * c.form y z := by
  have h := c.form_mul_mul_left (x + w) y z
  simp only [map_add, LinearMap.add_apply] at h
  rw [c.norm_add, c.form_mul_mul_left, c.form_mul_mul_left] at h
  linear_combination h

/-- **(I2')** `b(yx, zw) + b(yw, zx) = b(x, w) b(y, z)`. -/
theorem form_mul_mul_right₂ (x w y z : CayleyVector K) :
    c.form (μ y x) (μ z w) + c.form (μ y w) (μ z x) = c.form x w * c.form y z := by
  have h := c.form_mul_mul_right (x + w) y z
  simp only [map_add, LinearMap.add_apply] at h
  rw [c.norm_add, c.form_mul_mul_right, c.form_mul_mul_right] at h
  linear_combination h

/-- **(I3)** `b(xy, z) + b(y, xz) = T(x) b(y, z)`, that is `b(xy, z) = b(y, x̄z)`. -/
theorem form_mul_left (x y z : CayleyVector K) :
    c.form (μ x y) z + c.form y (μ x z) = c.trace x * c.form y z := by
  have h := c.form_mul_mul_left₂ x c.unit y z
  rw [c.unit_mul, c.unit_mul] at h
  exact h

/-- **(I3')** `b(yx, z) + b(y, zx) = T(x) b(y, z)`, that is `b(yx, z) = b(y, zx̄)`. -/
theorem form_mul_right (x y z : CayleyVector K) :
    c.form (μ y x) z + c.form y (μ z x) = c.trace x * c.form y z := by
  have h := c.form_mul_mul_right₂ x c.unit y z
  rw [c.mul_unit, c.mul_unit] at h
  exact h

/-- **(I4)** `x̄(xz) = N(x) z`, written as `T(x) xz - x(xz) = N(x) z`. -/
theorem mul_mul_left (x z : CayleyVector K) :
    c.trace x • μ x z - μ x (μ x z) = c.norm x • z := by
  apply c.eq_of_forall_form_eq
  intro w
  have h1 := c.form_mul_left x w (μ x z)
  have h2 := c.form_mul_mul_left x w z
  simp only [map_sub, map_smul, smul_eq_mul]
  linear_combination h2 - h1

/-- **(I4L)** `x̄(yz) + ȳ(xz) = b(x, y) z`. -/
theorem mul_mul_left₂ (x y z : CayleyVector K) :
    (c.trace x • μ y z - μ x (μ y z)) + (c.trace y • μ x z - μ y (μ x z)) =
      c.form x y • z := by
  apply c.eq_of_forall_form_eq
  intro w
  have h1 := c.form_mul_left x w (μ y z)
  have h2 := c.form_mul_left y w (μ x z)
  have h3 := c.form_mul_mul_left₂ x y w z
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  linear_combination h3 - h1 - h2

/-- **(I5)** Every vector satisfies `x² = T(x) x - N(x) 1`. -/
theorem mul_self (x : CayleyVector K) :
    μ x x = c.trace x • x - c.norm x • c.unit := by
  have h := c.mul_mul_left x c.unit
  rw [c.mul_unit] at h
  rw [← h]
  abel

/-- Linearization of `x² = T(x) x - N(x) 1`. -/
theorem mul_add_mul_comm (x y : CayleyVector K) :
    μ x y + μ y x = c.trace x • y + c.trace y • x - c.form x y • c.unit := by
  have h := c.mul_self (x + y)
  simp only [map_add, LinearMap.add_apply, c.trace_add, c.norm_add, c.mul_self x,
    c.mul_self y, add_smul, smul_add] at h
  rw [← sub_eq_zero] at h ⊢
  rw [← h]
  abel

/-- **Left alternativity** `x(xy) = x²y`. -/
theorem mul_mul_self_left (x y : CayleyVector K) : μ x (μ x y) = μ (μ x x) y := by
  have h := c.mul_mul_left x y
  rw [c.mul_self x, map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, c.unit_mul]
  rw [← h]
  abel

/-- The trace of a product: `T(xy) = T(x) T(y) - b(x, y)`. -/
theorem trace_mul (x y : CayleyVector K) :
    c.trace (μ x y) = c.trace x * c.trace y - c.form x y := by
  have h := c.form_mul_left x y c.unit
  rw [c.mul_unit, c.form_comm y x] at h
  change c.form (μ x y) c.unit = c.trace x * c.form y c.unit - c.form x y
  linear_combination h

end Langlands.GroupScheme.CayleyDatum
