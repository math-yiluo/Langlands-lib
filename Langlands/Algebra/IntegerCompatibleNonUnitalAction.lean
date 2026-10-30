import Langlands.Algebra.CompatibleNonUnitalAction
import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Canonical integer compatibility of additive nonunital actions

Derived implementation content for Renard's nonunital module conventions, printed pp. 5–6,
and the additive versus complex-linear morphism distinction in I.2.1, printed p. 14.
The integer scalars are the canonical scalars of each additive commutative group.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uV uW uP

namespace NonUnitalModule

variable {A : Type uA} [NonUnitalRing A] {V : Type uV} [AddCommGroup V]

/-- Integer scalar compatibility follows from additivity in the acting ring.
This is a named proof, not a global instance. -/
theorem int_isScalarTower [NonUnitalModule A V] : IsScalarTower ℤ A V where
  smul_assoc n a v :=
    ({ toFun := fun b : A => b • v
       map_zero' := NonUnitalModule.zero_smul v
       map_add' := fun b c => NonUnitalModule.add_smul b c v } : A →+ V).map_zsmul n a

/-- The original additive action as an actual nonunital integer-algebra homomorphism.
The canonical integer scalars impose no unit law on the original action. -/
def toIntLinearEndHom [h : NonUnitalModule A V] : A →ₙₐ[ℤ] Module.End ℤ V :=
  let := int_isScalarTower (A := A) (V := V)
  toLinearEndHom ℤ

@[simp] theorem toIntLinearEndHom_apply [NonUnitalModule A V] (a : A) (v : V) :
    toIntLinearEndHom (A := A) (V := V) a v = a • v := rfl

/-- Converting the integer-linear action back retains the original ambient action. -/
theorem ofLinearEndHom_toIntLinearEndHom [h : NonUnitalModule A V] :
    ofLinearEndHom (toIntLinearEndHom (A := A) (V := V)) = h :=
  ext fun _ _ => rfl

/-- The converse round trip is equality of actual homomorphisms. -/
theorem toIntLinearEndHom_ofLinearEndHom (ρ : A →ₙₐ[ℤ] Module.End ℤ V) :
    toIntLinearEndHom (h := ofLinearEndHom ρ) = ρ := by
  ext a v
  rfl

/-- Every additive nonunital action is canonically integer-compatible. -/
def equivIntLinearEndHom (A : Type uA) [NonUnitalRing A] (V : Type uV)
    [AddCommGroup V] : NonUnitalModule A V ≃ (A →ₙₐ[ℤ] Module.End ℤ V) where
  toFun h := toIntLinearEndHom (h := h)
  invFun := ofLinearEndHom
  left_inv _ := ofLinearEndHom_toIntLinearEndHom
  right_inv := toIntLinearEndHom_ofLinearEndHom

/-- The zero ambient action remains zero, including over a unital acting ring. -/
@[simp] theorem toIntLinearEndHom_zero :
    toIntLinearEndHom (h := (NonUnitalModule.zero : NonUnitalModule A V)) = 0 := by
  ext a v
  rfl

end NonUnitalModule

namespace NonUnitalModuleHom

variable {A : Type uA} [NonUnitalRing A]
  {V : Type uV} [AddCommGroup V] [NonUnitalModule A V]
  {W : Type uW} [AddCommGroup W] [NonUnitalModule A W]
  {P : Type uP} [AddCommGroup P] [NonUnitalModule A P]

/-- Every original additive intertwiner is automatically integer-linear. -/
def toIntLinearIntertwiner (f : NonUnitalModuleHom A V W) :
    LinearIntertwiner (NonUnitalModule.toIntLinearEndHom (A := A) (V := V))
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := W)) :=
  let := NonUnitalModule.int_isScalarTower (A := A) (V := V)
  let := NonUnitalModule.int_isScalarTower (A := A) (V := W)
  f.toLinearIntertwiner ℤ (fun n v => f.toAddMonoidHom.map_zsmul n v)

@[simp] theorem toIntLinearIntertwiner_apply (f : NonUnitalModuleHom A V W) (v : V) :
    f.toIntLinearIntertwiner v = f v := rfl

/-- The underlying map is Mathlib's canonical integer-linearization of the original map. -/
@[simp] theorem toIntLinearIntertwiner_toLinearMap (f : NonUnitalModuleHom A V W) :
    f.toIntLinearIntertwiner.toLinearMap = f.toAddMonoidHom.toIntLinearMap := rfl

/-- Exact correspondence with integer-linear intertwiners, using the published inverse
`ofLinearIntertwiner` on the same original ambient actions. -/
def equivIntLinearIntertwiner :
    NonUnitalModuleHom A V W ≃
      LinearIntertwiner (NonUnitalModule.toIntLinearEndHom (A := A) (V := V))
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := W)) where
  toFun := toIntLinearIntertwiner
  invFun f :=
    let := NonUnitalModule.int_isScalarTower (A := A) (V := V)
    let := NonUnitalModule.int_isScalarTower (A := A) (V := W)
    ofLinearIntertwiner f
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem equivIntLinearIntertwiner_symm_apply
    (f : LinearIntertwiner (NonUnitalModule.toIntLinearEndHom (A := A) (V := V))
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := W))) (v : V) :
    equivIntLinearIntertwiner.symm f v = f v := rfl

/-- Identity conversion retains the actual identity. -/
@[simp] theorem toIntLinearIntertwiner_id :
    (id A V).toIntLinearIntertwiner =
      LinearIntertwiner.id (NonUnitalModule.toIntLinearEndHom (A := A) (V := V)) := rfl

/-- Composition conversion retains the actual composition. -/
@[simp] theorem toIntLinearIntertwiner_comp (g : NonUnitalModuleHom A W P)
    (f : NonUnitalModuleHom A V W) :
    (g.comp f).toIntLinearIntertwiner =
      g.toIntLinearIntertwiner.comp f.toIntLinearIntertwiner := rfl

end NonUnitalModuleHom

end Langlands.Algebra
