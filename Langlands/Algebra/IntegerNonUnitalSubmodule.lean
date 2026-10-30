import Langlands.Algebra.IntegerCompatibleNonUnitalAction
import Langlands.Algebra.CompatibleUnitizationSubmodule

/-!
# Integer-compatible submodules of original additive actions

Derived implementation content for Renard's nonunital conventions, printed pp. 5–6,
and the scalar-linearity distinction in I.2.1, printed p. 14. The original action
is retained; integer scalars are the canonical scalars of the additive group.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalSubmodule

universe uA uM

variable {A : Type uA} [NonUnitalRing A] {M : Type uM}
  [AddCommGroup M] [NonUnitalModule A M]

/-- An original stable additive subgroup is canonically an integer-compatible submodule. -/
def toIntCompatible (S : NonUnitalSubmodule A M) :
    CompatibleSubmodule (NonUnitalModule.toIntLinearEndHom (A := A) (V := M)) where
  toSubmodule := S.toAddSubgroup.toIntSubmodule
  action_mem' a _ hm := S.smul_mem' a hm

/-- Forget integer scalars while keeping the original ambient action. -/
def ofIntCompatible
    (S : CompatibleSubmodule (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))) :
    NonUnitalSubmodule A M where
  toAddSubgroup := S.toSubmodule.toAddSubgroup
  smul_mem' a _ hm := S.action_mem a hm

@[simp] theorem mem_toIntCompatible {S : NonUnitalSubmodule A M} {m : M} :
    m ∈ S.toIntCompatible ↔ m ∈ S := Iff.rfl

@[simp] theorem mem_ofIntCompatible
    {S : CompatibleSubmodule (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))}
    {m : M} : m ∈ ofIntCompatible S ↔ m ∈ S := Iff.rfl

@[simp] theorem ofIntCompatible_toIntCompatible (S : NonUnitalSubmodule A M) :
    ofIntCompatible S.toIntCompatible = S :=
  SetLike.ext fun _ => Iff.rfl

@[simp] theorem toIntCompatible_ofIntCompatible
    (S : CompatibleSubmodule (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))) :
    (ofIntCompatible S).toIntCompatible = S :=
  CompatibleSubmodule.ext fun _ => Iff.rfl

/-- Original stable additive subgroups are exactly the integer-compatible submodules. -/
def intCompatibleOrderIso :
    NonUnitalSubmodule A M ≃o
      CompatibleSubmodule (NonUnitalModule.toIntLinearEndHom (A := A) (V := M)) where
  toFun := toIntCompatible
  invFun := ofIntCompatible
  left_inv := ofIntCompatible_toIntCompatible
  right_inv := toIntCompatible_ofIntCompatible
  map_rel_iff' := Iff.rfl

@[simp] theorem intCompatibleOrderIso_apply (S : NonUnitalSubmodule A M) :
    intCompatibleOrderIso S = S.toIntCompatible := rfl

@[simp] theorem intCompatibleOrderIso_symm_apply
    (S : CompatibleSubmodule (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))) :
    intCompatibleOrderIso.symm S = ofIntCompatible S := rfl

/-- Original stable additive subgroups are exactly the submodules for the actual
integer-unitized action, on the same carrier. The unitized module is selected locally. -/
def intUnitizedOrderIso :
    NonUnitalSubmodule A M ≃o
      (letI := CompatibleUnitization.module
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
       Submodule (Unitization ℤ A) M) :=
  intCompatibleOrderIso.trans
    (CompatibleUnitization.submoduleOrderIso
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := M)))

@[simp] theorem mem_intUnitizedOrderIso {S : NonUnitalSubmodule A M} {m : M} :
    (letI := CompatibleUnitization.module
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
     m ∈ intUnitizedOrderIso S) ↔ m ∈ S := Iff.rfl

@[simp] theorem mem_intUnitizedOrderIso_symm
    {p : letI := CompatibleUnitization.module (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
      Submodule (Unitization ℤ A) M} {m : M} :
    m ∈ intUnitizedOrderIso.symm p ↔
      (letI := CompatibleUnitization.module
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
       m ∈ p) := Iff.rfl

/-- The forward correspondence preserves the actual subset of the original carrier. -/
theorem coe_intUnitizedOrderIso (S : NonUnitalSubmodule A M) :
    (letI := CompatibleUnitization.module
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
     (intUnitizedOrderIso S : Set M)) = (S : Set M) := rfl

/-- The inverse correspondence preserves the actual subset of the original carrier. -/
theorem coe_intUnitizedOrderIso_symm
    (p : letI := CompatibleUnitization.module (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
      Submodule (Unitization ℤ A) M) :
    (intUnitizedOrderIso.symm p : Set M) =
      (letI := CompatibleUnitization.module
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
       (p : Set M)) := rfl

/-- Inclusion is unchanged by the integer-unitization correspondence. -/
theorem intUnitizedOrderIso_le_iff {S T : NonUnitalSubmodule A M} :
    (letI := CompatibleUnitization.module
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
     intUnitizedOrderIso S ≤ intUnitizedOrderIso T) ↔ S ≤ T :=
  intUnitizedOrderIso.le_iff_le

end Langlands.Algebra.NonUnitalSubmodule
