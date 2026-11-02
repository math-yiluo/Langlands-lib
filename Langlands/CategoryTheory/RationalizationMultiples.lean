import Langlands.CategoryTheory.RationalizationDenominators

/-! # Exact integral equations for prescribed rational multiples -/

noncomputable section

open CategoryTheory

set_option autoImplicit false

universe v u v' u'

namespace Langlands.Rationalization

variable {C : Type u} [Category.{v} C] [Preadditive C] {X Y : C}

/-- An exact integral cross-multiple equation retaining its prescribed rational ratio. -/
structure IntegralMultipleData (f g : X ⟶ Y) (q : ℚ) where
  left : ℤ
  right : ℤ
  left_ne_zero : left ≠ 0
  ratio : (right : ℚ) = (left : ℚ) * q
  equation : left • f = right • g

namespace IntegralMultipleData

variable {f g : X ⟶ Y} {q : ℚ}

/-- Exact integral data recover the equation with the original rational multiplier. -/
theorem rationalEquation (d : IntegralMultipleData f g q) :
    ofHom f = q • ofHom g := by
  have hl : (d.left : ℚ) ≠ 0 := Int.cast_ne_zero.mpr d.left_ne_zero
  apply smul_right_injective (M := Hom X Y) hl
  have h := congrArg (ofHom (X := X) (Y := Y)) d.equation
  simpa only [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, d.ratio, mul_smul] using h

/-- The right multiplier is nonzero whenever the prescribed rational ratio is nonzero. -/
theorem right_ne_zero (d : IntegralMultipleData f g q) (hq : q ≠ 0) :
    d.right ≠ 0 := by
  have hl : (d.left : ℚ) ≠ 0 := Int.cast_ne_zero.mpr d.left_ne_zero
  exact Int.cast_ne_zero.mp (d.ratio ▸ mul_ne_zero hl hq)

/-- Additive functors preserve supplied cross-multiple data and its rational ratio. -/
def map {C' : Type u'} [Category.{v'} C'] [Preadditive C']
    (F : C ⥤ C') [F.Additive] (d : IntegralMultipleData f g q) :
    IntegralMultipleData (F.map f) (F.map g) q where
  left := d.left
  right := d.right
  left_ne_zero := d.left_ne_zero
  ratio := d.ratio
  equation := by
    simpa only [Functor.map_zsmul] using congrArg (F.map (X := X) (Y := Y)) d.equation

end IntegralMultipleData

/-- A rational equation is equivalent to an exact integer cross-multiple equation,
without assuming injectivity of integral rationalization. -/
theorem ofHom_eq_smul_iff_nonempty_integralMultipleData
    (f g : X ⟶ Y) (q : ℚ) :
    ofHom f = q • ofHom g ↔ Nonempty (IntegralMultipleData f g q) := by
  constructor
  · intro h
    have hden : (q.den : ℚ) * q = q.num := by
      rw [mul_comm]
      exact Rat.mul_den_eq_num q
    have heq : ofHom ((q.den : ℤ) • f) = ofHom (q.num • g) := by
      simp only [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, h,
        smul_smul, hden]
    obtain ⟨k, hk, heq⟩ := (ofHom_eq_iff_exists_zsmul_eq _ _).mp heq
    refine ⟨{
      left := k * (q.den : ℤ)
      right := k * q.num
      left_ne_zero := mul_ne_zero hk (Int.natCast_ne_zero.mpr q.den_ne_zero)
      ratio := ?_
      equation := ?_ }⟩
    · simp only [Int.cast_mul, Int.cast_natCast, mul_assoc, hden]
    · simpa only [smul_smul] using heq
  · rintro ⟨d⟩
    exact d.rationalEquation

/-- Choose exact integral data for a supplied rational equation. -/
def integralMultipleData (f g : X ⟶ Y) (q : ℚ)
    (h : ofHom f = q • ofHom g) : IntegralMultipleData f g q :=
  Classical.choice ((ofHom_eq_smul_iff_nonempty_integralMultipleData f g q).mp h)

end Langlands.Rationalization
