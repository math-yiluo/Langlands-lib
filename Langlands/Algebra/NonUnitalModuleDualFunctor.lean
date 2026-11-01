import Langlands.Algebra.NonUnitalModuleDualMap
import Langlands.Algebra.NonUnitalModuleAdditive
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.CategoryTheory.Opposites

/-!
# Contravariant nondegenerate dual functors

Renard, I.4.1, printed p.22 / PDF p.28. Multiplicative double opposites
are transported explicitly back to the specified original ring.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDual

open CategoryTheory

universe uA uM uN

section DoubleOpposite

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M]

/-- The actual original-ring action transported from the multiplicative double opposite. -/
abbrev fromDoubleOppositeAction : NonUnitalModule A M where
  smul a m := MulOpposite.op (MulOpposite.op a) • m
  smul_zero a := smul_zero _
  smul_add a m n := smul_add _ m n
  mul_smul a b m := by
    change MulOpposite.op (MulOpposite.op (a * b)) • m =
      MulOpposite.op (MulOpposite.op a) • (MulOpposite.op (MulOpposite.op b) • m)
    rw [MulOpposite.op_mul, MulOpposite.op_mul, mul_smul]
  add_smul a b m := by
    change MulOpposite.op (MulOpposite.op (a + b)) • m =
      MulOpposite.op (MulOpposite.op a) • m + MulOpposite.op (MulOpposite.op b) • m
    rw [MulOpposite.op_add, MulOpposite.op_add, NonUnitalModule.add_smul]
  zero_smul m := by
    change MulOpposite.op (MulOpposite.op (0 : A)) • m = 0
    rw [MulOpposite.op_zero, MulOpposite.op_zero, NonUnitalModule.zero_smul]

@[simp] theorem fromDoubleOppositeAction_smul (a : A) (m : M) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    a • m = MulOpposite.op (MulOpposite.op a) • m := rfl

/-- Nondegeneracy transports through the actual double-op identification. -/
theorem fromDoubleOpposite_isNondegenerate (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    IsNondegenerate A M := by
  intro m
  obtain ⟨e, he⟩ := hM m
  let eA : Idempotent A := ⟨(e : Aᵐᵒᵖᵐᵒᵖ).unop.unop, by
    have h := congrArg (fun x : Aᵐᵒᵖᵐᵒᵖ => x.unop.unop) e.property.eq
    simpa only [IsIdempotentElem, MulOpposite.unop_mul] using h⟩
  exact ⟨eA, he⟩

/-- Scalar compatibility survives the explicit transport on the same carrier. -/
theorem fromDoubleOpposite_isScalarTower [Module ℂ A] [Module ℂ M]
    [IsScalarTower ℂ Aᵐᵒᵖᵐᵒᵖ M] :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    IsScalarTower ℂ A M := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  constructor
  intro c a m
  change MulOpposite.op (MulOpposite.op (c • a)) • m =
    c • (MulOpposite.op (MulOpposite.op a) • m)
  simpa only [MulOpposite.op_smul] using
    (smul_assoc c (MulOpposite.op (MulOpposite.op a)) m)

/-- Pointwise scalar multiplication still commutes with the transported original action. -/
theorem fromDoubleOpposite_smulCommClass [Module ℂ M]
    [SMulCommClass ℂ Aᵐᵒᵖᵐᵒᵖ M] :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    SMulCommClass ℂ A M := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  exact ⟨fun c a m => smul_comm c (MulOpposite.op (MulOpposite.op a)) m⟩

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ N]

/-- Transport of a double-op intertwiner keeps its entire additive map. -/
def fromDoubleOppositeMap (f : NonUnitalModuleHom Aᵐᵒᵖᵐᵒᵖ M N) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := A) (M := N)
    NonUnitalModuleHom A M N := by
  letI := fromDoubleOppositeAction (A := A) (M := M)
  letI := fromDoubleOppositeAction (A := A) (M := N)
  exact
    { toAddMonoidHom := f.toAddMonoidHom
      map_smul' a m := f.map_smul (MulOpposite.op (MulOpposite.op a)) m }

@[simp] theorem fromDoubleOppositeMap_toAddMonoidHom
    (f : NonUnitalModuleHom Aᵐᵒᵖᵐᵒᵖ M N) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := A) (M := N)
    (fromDoubleOppositeMap f).toAddMonoidHom = f.toAddMonoidHom := rfl

@[simp] theorem fromDoubleOppositeMap_apply
    (f : NonUnitalModuleHom Aᵐᵒᵖᵐᵒᵖ M N) (m : M) : fromDoubleOppositeMap f m = f m := rfl

@[simp] theorem fromDoubleOppositeMap_zero :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := A) (M := N)
    fromDoubleOppositeMap (0 : NonUnitalModuleHom Aᵐᵒᵖᵐᵒᵖ M N) = 0 := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fromDoubleOppositeAction (A := A) (M := N)
  apply NonUnitalModuleHom.ext
  intro m
  rfl

@[simp] theorem fromDoubleOppositeMap_add
    (f g : NonUnitalModuleHom Aᵐᵒᵖᵐᵒᵖ M N) :
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := A) (M := N)
    fromDoubleOppositeMap (f + g) = fromDoubleOppositeMap f + fromDoubleOppositeMap g := by
  let _ := fromDoubleOppositeAction (A := A) (M := M)
  let _ := fromDoubleOppositeAction (A := A) (M := N)
  apply NonUnitalModuleHom.ext
  intro m
  rfl

/-- This is a functor between the published original categories, not an identification of rings. -/
def fromDoubleOppositeFunctor :
    NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖᵐᵒᵖ ⥤ NondegenerateModuleCat.{uA, uM} A where
  obj M := by
    letI := fromDoubleOppositeAction (A := A) (M := M.obj)
    exact ⟨NonUnitalModuleCat.of A M.obj, fromDoubleOpposite_isNondegenerate M.property⟩
  map f := ObjectProperty.homMk (fromDoubleOppositeMap f.hom)
  map_id M := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    rfl

@[simp] theorem fromDoubleOppositeFunctor_obj_carrier
    (M : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖᵐᵒᵖ) :
    ((fromDoubleOppositeFunctor (A := A)).obj M).obj.carrier = M.obj.carrier := rfl

@[simp] theorem fromDoubleOppositeFunctor_obj_smul
    (M : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖᵐᵒᵖ) (a : A) (m : M.obj) :
    @SMul.smul A M.obj
      ((fromDoubleOppositeFunctor (A := A)).obj M).obj.isModule.toDistribSMul.toSMul a m =
      MulOpposite.op (MulOpposite.op a) • m := rfl

@[simp] theorem fromDoubleOppositeFunctor_map_hom
    {M N : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖᵐᵒᵖ} (f : M ⟶ N) :
    ((fromDoubleOppositeFunctor (A := A)).map f).hom = fromDoubleOppositeMap f.hom := rfl

end DoubleOpposite

section Functors

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

/-- The actual nondegenerate right dual as an object of the published original category. -/
def dualObject (hA : IsIdempotented A) (M : NondegenerateModuleCat.{uA, uM} A) :
    RightNondegenerateModuleCat.{uA, uM} A := by
  letI := fullAction hA M.property
  exact ⟨NonUnitalModuleCat.of Aᵐᵒᵖ (Dual hA M.property), isNondegenerate hA M.property⟩

@[simp] theorem dualObject_carrier (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    (dualObject hA M).obj.carrier = Dual hA M.property := rfl

/-- The bundled object's entire action on underlying functionals. -/
theorem dualObject_smul_val (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) (a : A) (φ : (dualObject hA M).obj) :
    (MulOpposite.op a • φ).val =
      φ.val.comp (NondegenerateScalars.toLinearEndHom ℂ hA M.property a) := rfl

@[simp] theorem dualObject_smul_apply (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) (a : A)
    (φ : (dualObject hA M).obj) (m : M.obj) :
    (MulOpposite.op a • φ).val m = φ.val (a • m) := rfl

/-- Duality reverses original left intertwiners into original right intertwiners. -/
def leftToRightFunctor (hA : IsIdempotented A) :
    (NondegenerateModuleCat.{uA, uM} A)ᵒᵖ ⥤ RightNondegenerateModuleCat.{uA, uM} A where
  obj M := dualObject hA M.unop
  map {M N} f := by
    letI := fullAction hA M.unop.property
    letI := fullAction hA N.unop.property
    exact ObjectProperty.homMk
      (pullback hA N.unop.property M.unop.property f.unop.hom)
  map_id M := by
    apply ObjectProperty.hom_ext
    exact pullback_id hA M.unop.property
  map_comp {M N P} f g := by
    apply ObjectProperty.hom_ext
    exact pullback_comp hA P.unop.property N.unop.property M.unop.property
      f.unop.hom g.unop.hom

@[simp] theorem leftToRightFunctor_obj (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    (leftToRightFunctor hA).obj (Opposite.op M) = dualObject hA M := rfl

@[simp] theorem leftToRightFunctor_obj_carrier (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((leftToRightFunctor hA).obj (Opposite.op M)).obj.carrier = Dual hA M.property := rfl

@[simp] theorem leftToRightFunctor_obj_smul_apply (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) (a : A)
    (φ : ((leftToRightFunctor hA).obj (Opposite.op M)).obj) (m : M.obj) :
    (MulOpposite.op a • φ).val m = φ.val (a • m) := rfl

/-- The entire bundled map is the pullback of the specified original intertwiner. -/
theorem leftToRightFunctor_map_hom (hA : IsIdempotented A)
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    letI := fullAction hA M.property
    letI := fullAction hA N.property
    ((leftToRightFunctor hA).map f.op).hom = pullback hA M.property N.property f.hom := rfl

theorem leftToRightFunctor_map_val (hA : IsIdempotented A)
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N)
    (φ : ((leftToRightFunctor hA).obj (Opposite.op N)).obj) :
    (NonUnitalModuleHom.toAddMonoidHom ((leftToRightFunctor hA).map f.op).hom φ).val =
      φ.val.comp (NondegenerateScalars.complexToLinearMap hA M.property N.property f.hom) :=
  rfl

@[simp] theorem leftToRightFunctor_map_apply (hA : IsIdempotented A)
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N)
    (φ : ((leftToRightFunctor hA).obj (Opposite.op N)).obj) (m : M.obj) :
    (NonUnitalModuleHom.toAddMonoidHom ((leftToRightFunctor hA).map f.op).hom φ).val m = φ.val (NonUnitalModuleHom.toAddMonoidHom f.hom m) := rfl

/-- The dual of a right module, explicitly transported to an actual left `A` action. -/
def rightDualObject (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA, uM} A) : NondegenerateModuleCat.{uA, uM} A :=
  (fromDoubleOppositeFunctor (A := A)).obj (dualObject hA.op M)

@[simp] theorem rightDualObject_carrier (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA, uM} A) :
    (rightDualObject hA M).obj.carrier = Dual hA.op M.property := rfl

theorem rightDualObject_smul_val (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA, uM} A) (a : A)
    (φ : (rightDualObject hA M).obj) :
    (a • φ).val =
      φ.val.comp (NondegenerateScalars.toLinearEndHom ℂ hA.op M.property (MulOpposite.op a)) :=
  rfl

@[simp] theorem rightDualObject_smul_apply (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA, uM} A) (a : A)
    (φ : (rightDualObject hA M).obj) (m : M.obj) :
    (a • φ).val m = φ.val (MulOpposite.op a • m) := rfl

/-- Apply opposite-ring duality and then the explicit multiplicative double-op transport. -/
def rightToLeftFunctor (hA : IsIdempotented A) :
    (RightNondegenerateModuleCat.{uA, uM} A)ᵒᵖ ⥤ NondegenerateModuleCat.{uA, uM} A :=
  leftToRightFunctor hA.op ⋙ fromDoubleOppositeFunctor (A := A)

@[simp] theorem rightToLeftFunctor_obj (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA, uM} A) :
    (rightToLeftFunctor hA).obj (Opposite.op M) = rightDualObject hA M := rfl

@[simp] theorem rightToLeftFunctor_obj_carrier (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA, uM} A) :
    ((rightToLeftFunctor hA).obj (Opposite.op M)).obj.carrier = Dual hA.op M.property := rfl

@[simp] theorem rightToLeftFunctor_obj_smul_apply (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA, uM} A) (a : A)
    (φ : ((rightToLeftFunctor hA).obj (Opposite.op M)).obj) (m : M.obj) :
    (a • φ).val m = φ.val (MulOpposite.op a • m) := rfl

/-- The actual left intertwiner keeps the whole pullback's additive function. -/
theorem rightToLeftFunctor_map_hom (hA : IsIdempotented A)
    {M N : RightNondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((rightToLeftFunctor hA).map f.op).hom =
      fromDoubleOppositeMap (pullback hA.op M.property N.property f.hom) := rfl

theorem rightToLeftFunctor_map_val (hA : IsIdempotented A)
    {M N : RightNondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N)
    (φ : ((rightToLeftFunctor hA).obj (Opposite.op N)).obj) :
    (NonUnitalModuleHom.toAddMonoidHom ((rightToLeftFunctor hA).map f.op).hom φ).val =
      φ.val.comp (NondegenerateScalars.complexToLinearMap hA.op M.property N.property f.hom) :=
  rfl

@[simp] theorem rightToLeftFunctor_map_apply (hA : IsIdempotented A)
    {M N : RightNondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N)
    (φ : ((rightToLeftFunctor hA).obj (Opposite.op N)).obj) (m : M.obj) :
    (NonUnitalModuleHom.toAddMonoidHom ((rightToLeftFunctor hA).map f.op).hom φ).val m = φ.val (NonUnitalModuleHom.toAddMonoidHom f.hom m) := rfl

end Functors

end Langlands.Algebra.NonUnitalModuleDual
