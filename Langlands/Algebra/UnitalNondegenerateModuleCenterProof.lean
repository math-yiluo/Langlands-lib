import Langlands.Algebra.NondegenerateModuleCenterStatements
import Langlands.Algebra.NondegenerateModuleNaturalEndClassificationProof

/-!
# Proof of the unital Remark of Renard I.1.7

Renard (9 July 2026), I.1.7, Remarque, printed p.13/PDF19. Proof of
`UnitalNondegenerateModuleCenterStatement`: for a unital ring `A`, every element of the centre
of the category of nondegenerate modules is multiplication by a unique central element of `A`,
and every central element arises.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra
namespace UnitalNondegenerateModuleCenterProof

open CategoryTheory

universe uA uM

section Unital

variable {A : Type uA} [Ring A]

/-- Multiplication by a central element, as an original module map. -/
def scalarHom (z : Subring.center A) (M : NondegenerateModuleCat.{uA, uM} A) :
    NonUnitalModuleHom A M.obj M.obj where
  toFun m := (z : A) • m
  map_zero' := smul_zero _
  map_add' := smul_add _
  map_smul' a m := by
    change (z : A) • a • m = a • (z : A) • m
    rw [← mul_smul, ← mul_smul, (Subring.mem_center_iff.mp z.property a).symm]

/-- Multiplication by a central element, as an element of the categorical centre. -/
def scalarCenter (z : Subring.center A) : NondegenerateModuleCenter.{uA, uM} A where
  app M := ObjectProperty.homMk (scalarHom z M)
  naturality M N f := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    exact (f.hom.map_smul (z : A) m).symm

/-- Every element of the categorical centre is multiplication by the unique central element
`θ_A(1)`, computed on the lifted regular object. -/
theorem existsUnique_center (θ : NondegenerateModuleCenter.{uA, max uA uM} A) :
    ∃! z : Subring.center A, ∀ (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj),
      (θ.app M).hom.toAddMonoidHom m = (z : A) • m := by
  have hA : IsIdempotented A := IsIdempotented.of_ring A
  let R := NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uM} hA
  let one : Idempotent A := ⟨1, IsIdempotentElem.one⟩
  let z : A := ((θ.app R).hom.toAddMonoidHom (ULift.up (1 : A))).down
  have hz : ∀ (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj),
      (θ.app M).hom.toAddMonoidHom m = z • m := by
    intro M m
    have h1 : (1 : A) • m = m := (exists_idempotent_smul_eq_iff_one_smul_eq m).mp (M.property m)
    exact NondegenerateModuleNaturalEndClassificationProof.app_eq_evaluation_smul.{uA, uM} hA
      (NondegenerateModuleCenter.forget θ) M m one h1
  have hcomm : ∀ a : A, a * z = z * a := by
    intro a
    have h1 : (θ.app R).hom.toAddMonoidHom (a • (ULift.up (1 : A) : R.obj)) =
        a • (θ.app R).hom.toAddMonoidHom (ULift.up (1 : A)) :=
      (θ.app R).hom.map_smul a _
    have h3 : (a • (ULift.up (1 : A) : R.obj)) = ULift.up a := congrArg ULift.up (mul_one a)
    rw [h3, hz R (ULift.up a)] at h1
    have h4 := congrArg ULift.down h1
    change z * a = a * z at h4
    exact h4.symm
  refine ⟨⟨z, Subring.mem_center_iff.mpr hcomm⟩, hz, ?_⟩
  intro w hw
  apply Subtype.ext
  have h := congrArg ULift.down (hw R (ULift.up (1 : A)))
  change z = (w : A) * 1 at h
  rw [mul_one] at h
  exact h.symm

end Unital

/-- Renard I.1.7, Remark: for unital `A` the centre of `M(A)` is the centre of `A`. -/
theorem unitalNondegenerateModuleCenter :
    UnitalNondegenerateModuleCenterStatement.{uA, uM} := by
  intro A _
  exact ⟨existsUnique_center.{uA, uM}, fun z => ⟨scalarCenter.{uA, max uA uM} z, fun _ _ => rfl⟩⟩

end UnitalNondegenerateModuleCenterProof
end Langlands.Algebra
