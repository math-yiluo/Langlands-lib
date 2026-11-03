import Langlands.AlgebraicGeometry.Picard.SquareZeroPicardObstruction
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Quotient classification of actual square-zero Picard lifting fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroPicardFibres

open SquareZeroUnitCohomology SquareZeroPicardObstruction

variable {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
  (i : Y ⟶ X) [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥)

/-- Actual ideal H¹ modulo the image of the actual degree-zero unit boundary. -/
abbrev infinitesimalClasses :=
  idealCohomology i 1 ⧸ (boundaryMap i hi 0).range

/-- The actual `1+a` Picard map with codomain restricted to the pullback kernel. -/
def oneAddToKernel : idealCohomology i 1 →+ (Group.pullback i).ker :=
  (oneAddPicardMap i hi).codRestrict (Group.pullback i).ker fun a =>
    (oneAddPicardMap_range_iff i hi _).mp ⟨a, rfl⟩

@[simp] lemma coe_oneAddToKernel (a : idealCohomology i 1) :
    (oneAddToKernel i hi a : Group X) = oneAddPicardMap i hi a := rfl

/-- Every actual Picard pullback-kernel class comes from actual ideal H¹. -/
theorem oneAddToKernel_surjective : Function.Surjective (oneAddToKernel i hi) := by
  intro x
  obtain ⟨a, ha⟩ := (oneAddPicardMap_range_iff i hi x.val).mpr x.property
  exact ⟨a, Subtype.ext ha⟩

/-- The kernel of the restricted map is the actual unit-H⁰ boundary image. -/
theorem oneAddToKernel_ker :
    (oneAddToKernel i hi).ker = (boundaryMap i hi 0).range := by
  rw [oneAddToKernel, AddMonoidHom.ker_codRestrict]
  ext a
  exact oneAddPicardMap_eq_zero_iff i hi a

/-- The quotient of actual ideal H¹ by unit boundaries is additively equivalent
 to the kernel of actual scheme Picard pullback. -/
def infinitesimalClassesEquivKernel :
    infinitesimalClasses i hi ≃+ (Group.pullback i).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (oneAddToKernel_ker i hi).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (oneAddToKernel i hi)
      (oneAddToKernel_surjective i hi))

@[simp] lemma infinitesimalClassesEquivKernel_mk (a : idealCohomology i 1) :
    infinitesimalClassesEquivKernel i hi (QuotientAddGroup.mk a) =
      oneAddToKernel i hi a := rfl

/-- Translation by a chosen lift identifies the actual pullback kernel with its fibre. -/
def kernelEquivFibre (y : Group Y) (x : Group X) (hx : Group.pullback i x = y) :
    (Group.pullback i).ker ≃ {x' : Group X // Group.pullback i x' = y} where
  toFun k := ⟨k.val + x, by rw [map_add, k.property, zero_add, hx]⟩
  invFun x' := ⟨x'.val - x, by
    change Group.pullback i (x'.val - x) = 0
    rw [map_sub, x'.property, hx, sub_self]⟩
  left_inv k := Subtype.ext (add_sub_cancel_right k.val x)
  right_inv x' := Subtype.ext (sub_add_cancel x'.val x)

omit [CompactSpace X] [CompactSpace Y] [IsClosedImmersion i] in
@[simp] lemma coe_kernelEquivFibre (y : Group Y) (x : Group X)
    (hx : Group.pullback i x = y) (k : (Group.pullback i).ker) :
    (kernelEquivFibre i y x hx k : Group X) = k.val + x := rfl

/-- A chosen actual Picard lift identifies its fibre with ideal H¹ modulo actual
unit-H⁰ boundaries. The fibre is used only as a type. -/
def infinitesimalClassesEquivFibre (y : Group Y) (x : Group X)
    (hx : Group.pullback i x = y) :
    infinitesimalClasses i hi ≃ {x' : Group X // Group.pullback i x' = y} :=
  (infinitesimalClassesEquivKernel i hi).toEquiv.trans (kernelEquivFibre i y x hx)

@[simp] lemma coe_infinitesimalClassesEquivFibre_mk (y : Group Y) (x : Group X)
    (hx : Group.pullback i x = y) (a : idealCohomology i 1) :
    (infinitesimalClassesEquivFibre i hi y x hx (QuotientAddGroup.mk a) : Group X) =
      oneAddPicardMap i hi a + x := rfl

end Langlands.AlgebraicGeometry.Picard.SquareZeroPicardFibres
