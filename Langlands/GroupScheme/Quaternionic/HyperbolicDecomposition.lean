import Langlands.GroupScheme.Quaternionic.HyperbolicPair

/-! # Hyperbolic projection and quadratic decomposition -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-- The polar form is linear over `D` in its first argument. -/
def polarFunctional (q : σ.QuadraticForms n) (y : n → D) : (n → D) →ₗ[D] D where
  toFun z := σ.sesqForm (σ.polar q) z y
  map_add' := fun z z' => σ.sesqForm_add_left _ z z' y
  map_smul' := fun a z => σ.sesqForm_smul_left _ a z y

@[simp] theorem polarFunctional_apply (q : σ.QuadraticForms n) (y z : n → D) :
    σ.polarFunctional q y z = σ.sesqForm (σ.polar q) z y := rfl

/-- The projection onto the hyperbolic plane, once `x,y` form a hyperbolic pair. -/
def hyperbolicProjection (q : σ.QuadraticForms n) (x y : n → D) :
    Module.End D (n → D) where
  toFun z := σ.polarFunctional q y z • x + σ.polarFunctional q x z • y
  map_add' := fun z z' => by simp only [LinearMap.map_add, add_smul]; abel
  map_smul' := fun a z => by
    simp only [LinearMap.map_smul, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply]

/-- The complementary projection onto the polar orthogonal complement. -/
def hyperbolicRemainder (q : σ.QuadraticForms n) (x y : n → D) :
    Module.End D (n → D) := LinearMap.id - σ.hyperbolicProjection q x y

@[simp] theorem hyperbolicProjection_apply (q : σ.QuadraticForms n) (x y z : n → D) :
    σ.hyperbolicProjection q x y z =
      σ.sesqForm (σ.polar q) z y • x + σ.sesqForm (σ.polar q) z x • y := rfl

@[simp] theorem hyperbolicRemainder_apply (q : σ.QuadraticForms n) (x y z : n → D) :
    σ.hyperbolicRemainder q x y z = z - σ.hyperbolicProjection q x y z := rfl

variable {σ} {q : σ.QuadraticForms n} {x y : n → D}

namespace IsHyperbolicPair

protected theorem symm (h : σ.IsHyperbolicPair q x y) : σ.IsHyperbolicPair q y x := by
  refine ⟨h.2.1, h.1, ?_⟩
  rw [← sesqForm_polar_swap, h.2.2, map_one]

protected theorem left_ne_zero (h : σ.IsHyperbolicPair q x y) : x ≠ 0 := by
  intro hx
  have := h.2.2
  rw [hx, sesqForm_zero_left] at this
  exact zero_ne_one this

protected theorem right_ne_zero (h : σ.IsHyperbolicPair q x y) : y ≠ 0 := h.symm.left_ne_zero

@[simp] theorem hyperbolicProjection_left (h : σ.IsHyperbolicPair q x y) :
    σ.hyperbolicProjection q x y x = x := by
  simp only [hyperbolicProjection_apply, h.2.2,
    sesqForm_polar_self_eq_zero σ q x h.1, one_smul, zero_smul, add_zero]

@[simp] theorem hyperbolicProjection_right (h : σ.IsHyperbolicPair q x y) :
    σ.hyperbolicProjection q x y y = y := by
  simp only [hyperbolicProjection_apply, h.symm.2.2,
    sesqForm_polar_self_eq_zero σ q y h.2.1, one_smul, zero_smul, zero_add]

theorem hyperbolicRemainder_pair_left (h : σ.IsHyperbolicPair q x y) (z : n → D) :
    σ.sesqForm (σ.polar q) (σ.hyperbolicRemainder q x y z) x = 0 := by
  change σ.polarFunctional q x (z - σ.hyperbolicProjection q x y z) = 0
  rw [LinearMap.map_sub, hyperbolicProjection_apply, LinearMap.map_add]
  simp only [LinearMap.map_smul, polarFunctional_apply, h.symm.2.2,
    sesqForm_polar_self_eq_zero σ q x h.1, smul_eq_mul, mul_zero, mul_one,
    zero_add, sub_self]

theorem hyperbolicRemainder_pair_right (h : σ.IsHyperbolicPair q x y) (z : n → D) :
    σ.sesqForm (σ.polar q) (σ.hyperbolicRemainder q x y z) y = 0 := by
  change σ.polarFunctional q y (z - σ.hyperbolicProjection q x y z) = 0
  rw [LinearMap.map_sub, hyperbolicProjection_apply, LinearMap.map_add]
  simp only [LinearMap.map_smul, polarFunctional_apply, h.2.2,
    sesqForm_polar_self_eq_zero σ q y h.2.1, smul_eq_mul, mul_zero, mul_one,
    add_zero, sub_self]

theorem hyperbolicProjection_idempotent (h : σ.IsHyperbolicPair q x y) (z : n → D) :
    σ.hyperbolicProjection q x y (σ.hyperbolicProjection q x y z) =
      σ.hyperbolicProjection q x y z := by
  rw [hyperbolicProjection_apply σ q x y z,
    LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
    h.hyperbolicProjection_left, h.hyperbolicProjection_right]

theorem hyperbolicRemainder_projection (h : σ.IsHyperbolicPair q x y) (z : n → D) :
    σ.hyperbolicRemainder q x y (σ.hyperbolicProjection q x y z) = 0 := by
  rw [hyperbolicRemainder_apply, h.hyperbolicProjection_idempotent, sub_self]

/-- On the hyperbolic plane the quadratic value is the class of `a σ(b)`. -/
theorem quadraticValue_plane (h : σ.IsHyperbolicPair q x y) (a b : D) :
    σ.quadraticValue (a • x + b • y) q =
      (Submodule.Quotient.mk (a * σ b) : D ⧸ σ.alternatingSubspace) := by
  rw [quadraticValue_add, quadraticValue_smul_eq_zero σ a x q h.1,
    quadraticValue_smul_eq_zero σ b y q h.2.1,
    sesqForm_smul_left, sesqForm_smul_right, h.2.2, one_mul, zero_add, zero_add]

/-- The plane and its complementary projection are orthogonal for the polar form. -/
theorem hyperbolicProjection_pair_remainder (h : σ.IsHyperbolicPair q x y) (z z' : n → D) :
    σ.sesqForm (σ.polar q) (σ.hyperbolicProjection q x y z)
      (σ.hyperbolicRemainder q x y z') = 0 := by
  have hx : σ.sesqForm (σ.polar q) x (σ.hyperbolicRemainder q x y z') = 0 := by
    rw [← sesqForm_polar_swap, h.hyperbolicRemainder_pair_left, map_zero]
  have hy : σ.sesqForm (σ.polar q) y (σ.hyperbolicRemainder q x y z') = 0 := by
    rw [← sesqForm_polar_swap, h.hyperbolicRemainder_pair_right, map_zero]
  rw [hyperbolicProjection_apply, sesqForm_add_left, sesqForm_smul_left,
    sesqForm_smul_left, hx, hy, mul_zero, mul_zero, add_zero]

/-- The quadratic form splits into its hyperbolic-plane value and complementary value. -/
theorem quadraticValue_decomposition (h : σ.IsHyperbolicPair q x y) (z : n → D) :
    σ.quadraticValue z q =
      (Submodule.Quotient.mk
        (σ.sesqForm (σ.polar q) z y * σ (σ.sesqForm (σ.polar q) z x)) :
          D ⧸ σ.alternatingSubspace) +
      σ.quadraticValue (σ.hyperbolicRemainder q x y z) q := by
  conv_lhs => rw [show z = σ.hyperbolicProjection q x y z +
    σ.hyperbolicRemainder q x y z by rw [hyperbolicRemainder_apply]; abel]
  rw [quadraticValue_add, h.hyperbolicProjection_pair_remainder,
    Submodule.Quotient.mk_zero, add_zero, hyperbolicProjection_apply, h.quadraticValue_plane]

end IsHyperbolicPair

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
