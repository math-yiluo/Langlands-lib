import Langlands.GroupScheme.Quaternionic.HyperbolicDecomposition

/-! # Central-scalar hyperbolic scaling -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-- Scale the two hyperbolic coordinates by a central unit and its inverse,
fixing the complementary projection. -/
def hyperbolicScaling (q : σ.QuadraticForms n) (x y : n → D) (t : Kˣ) :
    Module.End D (n → D) :=
  (t : K) • (σ.polarFunctional q y).smulRight x +
    ((t⁻¹ : Kˣ) : K) • (σ.polarFunctional q x).smulRight y +
    σ.hyperbolicRemainder q x y

@[simp] theorem hyperbolicScaling_apply (q : σ.QuadraticForms n) (x y : n → D)
    (t : Kˣ) (z : n → D) :
    σ.hyperbolicScaling q x y t z =
      (t : K) • (σ.sesqForm (σ.polar q) z y • x) +
      ((t⁻¹ : Kˣ) : K) • (σ.sesqForm (σ.polar q) z x • y) +
      σ.hyperbolicRemainder q x y z := rfl

/-- Central scalars can be pulled out of the first polar argument. -/
theorem sesqForm_polar_smul_left (q : σ.QuadraticForms n) (c : K) (z z' : n → D) :
    σ.sesqForm (σ.polar q) (c • z) z' = c • σ.sesqForm (σ.polar q) z z' :=
  (σ.polarFunctional q z').map_smul_of_tower c z

variable {σ} {q : σ.QuadraticForms n} {x y : n → D}

namespace IsHyperbolicPair

@[simp] theorem hyperbolicRemainder_left (h : σ.IsHyperbolicPair q x y) :
    σ.hyperbolicRemainder q x y x = 0 := by
  rw [hyperbolicRemainder_apply, h.hyperbolicProjection_left, sub_self]

@[simp] theorem hyperbolicRemainder_right (h : σ.IsHyperbolicPair q x y) :
    σ.hyperbolicRemainder q x y y = 0 := by
  rw [hyperbolicRemainder_apply, h.hyperbolicProjection_right, sub_self]

theorem hyperbolicRemainder_idempotent (h : σ.IsHyperbolicPair q x y) (z : n → D) :
    σ.hyperbolicRemainder q x y (σ.hyperbolicRemainder q x y z) =
      σ.hyperbolicRemainder q x y z := by
  change σ.hyperbolicRemainder q x y (z - σ.hyperbolicProjection q x y z) = _
  rw [LinearMap.map_sub, h.hyperbolicRemainder_projection, sub_zero]

@[simp] theorem hyperbolicScaling_left (h : σ.IsHyperbolicPair q x y) (t : Kˣ) :
    σ.hyperbolicScaling q x y t x = (t : K) • x := by
  simp only [hyperbolicScaling_apply, h.2.2,
    sesqForm_polar_self_eq_zero σ q x h.1, one_smul, zero_smul,
    h.hyperbolicRemainder_left, smul_zero, add_zero]

@[simp] theorem hyperbolicScaling_right (h : σ.IsHyperbolicPair q x y) (t : Kˣ) :
    σ.hyperbolicScaling q x y t y = ((t⁻¹ : Kˣ) : K) • y := by
  simp only [hyperbolicScaling_apply, h.symm.2.2,
    sesqForm_polar_self_eq_zero σ q y h.2.1, one_smul, zero_smul,
    h.hyperbolicRemainder_right, smul_zero, zero_add, add_zero]

theorem hyperbolicScaling_pair_right (h : σ.IsHyperbolicPair q x y) (t : Kˣ) (z : n → D) :
    σ.sesqForm (σ.polar q) (σ.hyperbolicScaling q x y t z) y =
      (t : K) • σ.sesqForm (σ.polar q) z y := by
  simp only [hyperbolicScaling_apply, sesqForm_add_left, sesqForm_polar_smul_left,
    sesqForm_smul_left, h.2.2, sesqForm_polar_self_eq_zero σ q y h.2.1,
    h.hyperbolicRemainder_pair_right, mul_one, mul_zero, smul_zero, add_zero]

theorem hyperbolicScaling_pair_left (h : σ.IsHyperbolicPair q x y) (t : Kˣ) (z : n → D) :
    σ.sesqForm (σ.polar q) (σ.hyperbolicScaling q x y t z) x =
      ((t⁻¹ : Kˣ) : K) • σ.sesqForm (σ.polar q) z x := by
  simp only [hyperbolicScaling_apply, sesqForm_add_left, sesqForm_polar_smul_left,
    sesqForm_smul_left, h.symm.2.2, sesqForm_polar_self_eq_zero σ q x h.1,
    h.hyperbolicRemainder_pair_left, mul_one, mul_zero, smul_zero, zero_add, add_zero]

theorem hyperbolicRemainder_scaling (h : σ.IsHyperbolicPair q x y) (t : Kˣ) (z : n → D) :
    σ.hyperbolicRemainder q x y (σ.hyperbolicScaling q x y t z) =
      σ.hyperbolicRemainder q x y z := by
  simp only [hyperbolicScaling_apply, LinearMap.map_add, LinearMap.map_smul_of_tower,
    h.hyperbolicRemainder_left, h.hyperbolicRemainder_right,
    h.hyperbolicRemainder_idempotent, smul_zero, zero_add]

@[simp] theorem hyperbolicScaling_one (_h : σ.IsHyperbolicPair q x y) :
    σ.hyperbolicScaling q x y 1 = 1 := by
  apply LinearMap.ext
  intro z
  change σ.hyperbolicScaling q x y 1 z = z
  simp only [hyperbolicScaling_apply, inv_one, Units.val_one, one_smul,
    hyperbolicRemainder_apply, hyperbolicProjection_apply]
  abel

theorem hyperbolicScaling_mul (h : σ.IsHyperbolicPair q x y) (t s : Kˣ) :
    σ.hyperbolicScaling q x y (t * s) =
      σ.hyperbolicScaling q x y t * σ.hyperbolicScaling q x y s := by
  apply LinearMap.ext
  intro z
  change σ.hyperbolicScaling q x y (t * s) z =
    σ.hyperbolicScaling q x y t (σ.hyperbolicScaling q x y s z)
  rw [hyperbolicScaling_apply, hyperbolicScaling_apply,
    h.hyperbolicScaling_pair_right, h.hyperbolicScaling_pair_left,
    h.hyperbolicRemainder_scaling]
  simp only [Units.val_mul, mul_inv_rev,
    smul_assoc, smul_smul, mul_comm]

/-- Central-scalar hyperbolic scaling preserves the full quotient-valued quadratic form. -/
theorem quadraticValue_hyperbolicScaling (h : σ.IsHyperbolicPair q x y)
    (t : Kˣ) (z : n → D) :
    σ.quadraticValue (σ.hyperbolicScaling q x y t z) q = σ.quadraticValue z q := by
  rw [h.quadraticValue_decomposition (σ.hyperbolicScaling q x y t z),
    h.hyperbolicScaling_pair_right, h.hyperbolicScaling_pair_left,
    h.hyperbolicRemainder_scaling, map_smul, smul_mul_smul_comm,
    Units.mul_inv, one_smul, ← h.quadraticValue_decomposition]

/-- The scaling maps define a homomorphism into the units of the actual endomorphism ring. -/
def hyperbolicScalingHom (h : σ.IsHyperbolicPair q x y) :
    Kˣ →* (Module.End D (n → D))ˣ where
  toFun t :=
    { val := σ.hyperbolicScaling q x y t
      inv := σ.hyperbolicScaling q x y t⁻¹
      val_inv := by rw [← h.hyperbolicScaling_mul, mul_inv_cancel, h.hyperbolicScaling_one]
      inv_val := by rw [← h.hyperbolicScaling_mul, inv_mul_cancel, h.hyperbolicScaling_one] }
  map_one' := Units.ext h.hyperbolicScaling_one
  map_mul' t s := Units.ext (h.hyperbolicScaling_mul t s)

@[simp] theorem hyperbolicScalingHom_val (h : σ.IsHyperbolicPair q x y) (t : Kˣ) :
    (h.hyperbolicScalingHom t : Module.End D (n → D)) =
      σ.hyperbolicScaling q x y t := rfl

/-- The action on the first nonzero singular vector detects the central unit. -/
theorem hyperbolicScalingHom_injective (h : σ.IsHyperbolicPair q x y) :
    Function.Injective h.hyperbolicScalingHom := by
  intro t s he
  have hx := congrArg (fun a : (Module.End D (n → D))ˣ => (a : Module.End D (n → D)) x) he
  change σ.hyperbolicScaling q x y t x = σ.hyperbolicScaling q x y s x at hx
  rw [h.hyperbolicScaling_left, h.hyperbolicScaling_left] at hx
  exact Units.ext (smul_left_injective K h.left_ne_zero hx)

end IsHyperbolicPair

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
