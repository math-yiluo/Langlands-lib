import Langlands.GroupScheme.Examples.SU3RootFiltration

/-! # Scaling the quadratic root coordinates and their depths -/

noncomputable section

namespace Langlands.GroupScheme.SU3Root

universe u v

namespace Parameters

section Ring

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  {c : RingInvolution A} {d : RingInvolution B}

/-- Coordinate scaling by a scalar, with the norm factor on the second coordinate. -/
def scale (a : A) : Parameters c →* Parameters c where
  toFun x := ⟨(a * x.first, (a * c.bar a) * x.second), by
    change (a * c.bar a) * x.second + c.bar ((a * c.bar a) * x.second) =
      (a * x.first) * c.bar (a * x.first)
    simp only [map_mul, RingInvolution.bar_bar]
    calc
      _ = (a * c.bar a) * (x.second + c.bar x.second) := by ring
      _ = _ := by rw [equation]; ring⟩
  map_one' := by
    apply ext
    · change a * 0 = 0
      exact mul_zero a
    · change (a * c.bar a) * 0 = 0
      exact mul_zero _
  map_mul' x y := by
    apply ext
    · change a * (x.first + y.first) = a * x.first + a * y.first
      ring
    · change (a * c.bar a) * (x.second + y.second + x.first * c.bar y.first) =
        (a * c.bar a) * x.second + (a * c.bar a) * y.second +
          (a * x.first) * c.bar (a * y.first)
      rw [map_mul]
      ring

@[simp] theorem first_scale (a : A) (x : Parameters c) :
    (scale a x).first = a * x.first := rfl

@[simp] theorem second_scale (a : A) (x : Parameters c) :
    (scale a x).second = (a * c.bar a) * x.second := rfl

@[simp] theorem scale_one_apply (x : Parameters c) : scale (1 : A) x = x := by
  ext <;> simp

theorem scale_mul_apply (a b : A) (x : Parameters c) :
    scale (a * b) x = scale a (scale b x) := by
  ext <;> simp only [first_scale, second_scale, map_mul] <;> ring

/-- Scaling by a unit is an automorphism, with the reciprocal scaling as inverse. -/
def scaleEquiv (a : Aˣ) : Parameters c ≃* Parameters c where
  toFun := scale (a : A)
  invFun := scale (↑a⁻¹ : A)
  left_inv x := by rw [← scale_mul_apply, Units.inv_mul, scale_one_apply]
  right_inv x := by rw [← scale_mul_apply, Units.mul_inv, scale_one_apply]
  map_mul' := (scale (a : A)).map_mul

@[simp] theorem scaleEquiv_apply (a : Aˣ) (x : Parameters c) :
    scaleEquiv a x = scale (a : A) x := rfl

/-- The same scalar map restricts to the literal central subgroup. -/
def centralScale (a : A) : central c →* central c where
  toFun z := ⟨scale a z.val, by
    simp only [mem_central, first_scale, (mem_central z.val).mp z.property, mul_zero]⟩
  map_one' := Subtype.ext ((scale a).map_one)
  map_mul' x y := Subtype.ext ((scale a).map_mul x.val y.val)

@[simp] theorem centralScale_val (a : A) (z : central c) :
    (centralScale a z).val = scale a z.val := rfl

/-- Scaling commutes with any involution-compatible coefficient map. -/
theorem scale_map (f : A →+* B) (hf : ∀ x, f (c.bar x) = d.bar (f x))
    (a : A) (x : Parameters c) :
    map f hf (scale a x) = scale (f a) (map f hf x) := by
  ext <;> simp only [first_map, second_map, first_scale, second_scale, map_mul, hf]

end Ring

section Valuation

variable {L : Type u} [Field L] {c : RingInvolution L}
  (omega : AddValuation L (WithTop ℝ))
  (hinv : ∀ z : L, omega (c.bar z) = omega z)

private theorem halfTop_add_add (s t : WithTop ℝ) :
    halfTop ((s + s) + t) = s + halfTop t := by
  cases s using WithTop.recTopCoe with
  | top => simp
  | coe s =>
    cases t using WithTop.recTopCoe with
    | top => simp
    | coe t =>
      simp only [← WithTop.coe_add, halfTop_coe]
      congr 1
      ring

include hinv in
/-- Scaling translates the root depth by the value of the first-coordinate scalar. -/
theorem depthA_scale (a : L) (x : Parameters c) :
    depthA omega (scale a x) = omega a + depthA omega x := by
  simp only [depthA, second_scale, omega.map_mul, hinv]
  exact halfTop_add_add (omega a) (omega x.second)

include hinv in
/-- On the central subgroup the depth shift is twice that scalar value. -/
theorem depthDouble_centralScale (a : L) (z : central c) :
    depthDouble omega (centralScale a z) =
      (omega a + omega a) + depthDouble omega z := by
  simp only [depthDouble, centralScale_val, second_scale, omega.map_mul, hinv]

include hinv in
/-- Finite scalar value gives an exact shifted root-filtration pullback. -/
theorem comap_filtration_scale (a : Lˣ) (t r : ℝ)
    (ha : omega (a : L) = (t : WithTop ℝ)) :
    (filtration omega hinv (r + t)).comap (scale (a : L)) =
      filtration omega hinv r := by
  ext x
  change scale (a : L) x ∈ filtration omega hinv (r + t) ↔
    x ∈ filtration omega hinv r
  rw [mem_filtration_iff_depth, mem_filtration_iff_depth, depthA_scale omega hinv, ha]
  cases depthA omega x using WithTop.recTopCoe with
  | top => simp
  | coe q =>
    simp only [← WithTop.coe_add, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

include hinv in
/-- The central filtration shifts by twice the scalar value, in the ambient group. -/
theorem comap_centralFiltration_scale (a : Lˣ) (t r : ℝ)
    (ha : omega (a : L) = (t : WithTop ℝ)) :
    (centralFiltration omega hinv (r + 2 * t)).comap (scale (a : L)) =
      centralFiltration omega hinv r := by
  ext x
  change (a * x.first = 0 ∧
      (↑(r + 2 * t) : WithTop ℝ) ≤ omega ((a * c.bar a) * x.second)) ↔
    (x.first = 0 ∧ (r : WithTop ℝ) ≤ omega x.second)
  rw [mul_eq_zero, or_iff_right (Units.ne_zero a), omega.map_mul,
    omega.map_mul, hinv, ha]
  cases omega x.second using WithTop.recTopCoe with
  | top => simp
  | coe q =>
    simp only [← WithTop.coe_add, WithTop.coe_le_coe]
    constructor
    · rintro ⟨hx, hq⟩
      exact ⟨hx, by linarith⟩
    · rintro ⟨hx, hq⟩
      exact ⟨hx, by linarith⟩

end Valuation

end Parameters
end Langlands.GroupScheme.SU3Root
