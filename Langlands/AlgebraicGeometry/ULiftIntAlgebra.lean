import Mathlib

/-! # `ULift ℤ` as the base ring of absolute constructions in an arbitrary universe -/

noncomputable section

namespace Langlands.ULiftInt

universe u v w

/-- Every commutative ring is an algebra over `ULift ℤ`, through the unique ring map
`ULift ℤ → ℤ → A`. This is a definition, to be used as a local instance. -/
abbrev algebra (A : Type v) [CommRing A] : Algebra (ULift.{u} ℤ) A :=
  ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom).toAlgebra

theorem algebraMap_apply (A : Type v) [CommRing A] (n : ULift.{u} ℤ) :
    @algebraMap (ULift.{u} ℤ) A _ _ (algebra A) n = (n.down : A) :=
  rfl

/-- Two ring maps out of `ULift ℤ` are equal. -/
theorem ringHom_ext {A : Type v} [Semiring A] (f g : ULift.{u} ℤ →+* A) : f = g := by
  have h := RingHom.ext_int (f.comp ULift.ringEquiv.symm.toRingHom)
    (g.comp ULift.ringEquiv.symm.toRingHom)
  ext n
  exact congrArg (fun φ : ℤ →+* A => φ n.down) h

/-- A ring map, as an algebra map over `ULift ℤ` for the algebra structures `algebra`. -/
def toAlgHom {A : Type v} {B : Type w} [CommRing A] [CommRing B] (φ : A →+* B) :
    @AlgHom (ULift.{u} ℤ) A B _ _ _ (algebra A) (algebra B) :=
  @AlgHom.mk (ULift.{u} ℤ) A B _ _ _ (algebra A) (algebra B) φ fun n => by
    change φ ((n.down : ℤ) : A) = ((n.down : ℤ) : B)
    exact map_intCast φ n.down

@[simp] theorem toAlgHom_toRingHom {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (φ : A →+* B) : (toAlgHom.{u} φ : A →+* B) = φ :=
  rfl

instance isNoetherianRing : IsNoetherianRing (ULift.{u} ℤ) :=
  isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm

end Langlands.ULiftInt
