import Langlands.Algebra.NonUnitalBimoduleTensor
import Langlands.Algebra.NonUnitalModuleRestrictScalars
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Unital scalar extension over possibly noncommutative rings

The original balanced quotient, with its actual residual left action upgraded
by the unit law. Renard (9 July 2026), A.V.2, printed pp.260–261 / PDF266–267.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.UnitalScalarExtension

open CategoryTheory MulOpposite

universe uB uA uM uN uP uZ uk

variable {B : Type uB} {A : Type uA} [Ring B] [Ring A] (φ : B →+* A)

/-- Right multiplication through the specified unital scalar homomorphism. -/
@[instance_reducible]
def rightModule : NonUnitalModule Bᵐᵒᵖ A :=
  NonUnitalModuleRestrictScalars.module φ.op.toNonUnitalRingHom
    (NonUnitalModule.rightRegular A)

theorem rightModule_action (b : B) (a : A) :
    NonUnitalModule.toEndHom (rightModule φ) (op b) a = a * φ b := rfl

/-- The exact formula `op b • a = a * φ b` for the selected action. -/
theorem rightModule_smul (b : B) (a : A) :
    @HSMul.hSMul Bᵐᵒᵖ A A
        (@instHSMul Bᵐᵒᵖ A (@NonUnitalModule.actionSMul Bᵐᵒᵖ A _ _ (rightModule φ)))
        (op b) a = a * φ b := rfl

/-- The specified left multiplication commutes with the specified right action. -/
theorem actionsCommute :
    @ActionsCommute A B A _ _ _ (NonUnitalModule.regular A) (rightModule φ) :=
  fun a b x => (mul_assoc a x (φ b)).symm

variable (M : Type uM) [AddCommGroup M] [Module B M]

/-- Exactly the published integer-tensor balancing quotient, for the selected actions. -/
abbrev Tensor : Type (max uA uM) :=
  letI := rightModule φ
  letI := NonUnitalModule.ofModule B M
  NonUnitalModuleTensor.Tensor B A M

instance tensorAddCommGroup : AddCommGroup (Tensor φ M) := by
  letI := rightModule φ
  letI := NonUnitalModule.ofModule B M
  exact NonUnitalModuleTensor.addCommGroup B A M

/-- The additive group is the published quotient group. -/
theorem tensorAddCommGroup_eq :
    letI := rightModule φ
    letI := NonUnitalModule.ofModule B M
    tensorAddCommGroup φ M = NonUnitalModuleTensor.addCommGroup B A M := rfl

/-- The actual quotient value of the pure tensor. -/
def tmul (a : A) (m : M) : Tensor φ M := by
  letI := rightModule φ
  letI := NonUnitalModule.ofModule B M
  exact NonUnitalModuleTensor.tmul B A M a m

theorem tmul_eq (a : A) (m : M) :
    letI := rightModule φ
    letI := NonUnitalModule.ofModule B M
    tmul φ M a m = NonUnitalModuleTensor.tmul B A M a m := rfl

/-- The named residual left multiplication on the same quotient. -/
@[instance_reducible]
def residualModule : NonUnitalModule A (Tensor φ M) := by
  letI := rightModule φ
  letI := NonUnitalModule.regular A
  letI := NonUnitalModule.ofModule B M
  exact NonUnitalBimoduleTensor.leftModule (actionsCommute φ) M

theorem residualModule_eq :
    letI := rightModule φ
    letI := NonUnitalModule.regular A
    letI := NonUnitalModule.ofModule B M
    residualModule φ M = NonUnitalBimoduleTensor.leftModule (actionsCommute φ) M := rfl

theorem residualModule_action (a x : A) (m : M) :
    NonUnitalModule.toEndHom (residualModule φ M) a (tmul φ M x m) = tmul φ M (a * x) m :=
  rfl

/-- The residual action of `1` is the identity, by pure-tensor extensionality. -/
theorem residualModule_one :
    NonUnitalModule.toEndHom (residualModule φ M) 1 = AddMonoidHom.id (Tensor φ M) := by
  let _ := rightModule φ
  let _ := NonUnitalModule.ofModule B M
  exact NonUnitalModuleTensor.hom_ext B fun a m => by
    change NonUnitalModuleTensor.tmul B A M (1 * a) m =
      NonUnitalModuleTensor.tmul B A M a m
    rw [one_mul]

/-- The same residual action is unital, hence defines an ordinary module. -/
@[instance_reducible]
def module : Module A (Tensor φ M) := by
  letI := residualModule φ M
  exact NonUnitalModule.toModule fun t => DFunLike.congr_fun (residualModule_one φ M) t

/-- The ordinary action is literally the residual action. -/
theorem module_smul (a : A) (t : Tensor φ M) :
    letI := module φ M
    a • t = NonUnitalModule.toEndHom (residualModule φ M) a t := rfl

/-- Bundle precisely that quotient group and its unital residual action. -/
def tensorObj : ModuleCat.{max uA uM} A :=
  @ModuleCat.of A _ (Tensor φ M) (tensorAddCommGroup φ M) (module φ M)

theorem tensorObj_carrier : (tensorObj φ M).carrier = Tensor φ M := rfl

theorem tensorObj_addCommGroup : (tensorObj φ M).isAddCommGroup = tensorAddCommGroup φ M := rfl

theorem tensorObj_module : (tensorObj φ M).isModule = module φ M := rfl

theorem smul_tmul (a x : A) (m : M) :
    letI := module φ M
    a • tmul φ M x m = tmul φ M (a * x) m := rfl

theorem tmul_balanced (b : B) (a : A) (m : M) :
    tmul φ M (a * φ b) m = tmul φ M a (b • m) := by
  let _ := rightModule φ
  let _ := NonUnitalModule.ofModule B M
  exact NonUnitalModuleTensor.tmul_balanced B A M b a m

/-- Extensionality for actual linear maps out of the constructed quotient. -/
theorem hom_ext {Z : Type uZ} [AddCommGroup Z] [Module A Z]
    {f g : tensorObj φ M →ₗ[A] Z}
    (h : ∀ a m, f (tmul φ M a m) = g (tmul φ M a m)) : f = g := by
  let _ := rightModule φ
  let _ := NonUnitalModule.ofModule B M
  apply LinearMap.toAddMonoidHom_injective
  exact NonUnitalModuleTensor.hom_ext B h

variable {M} {N : Type uN} {P : Type uP}
  [AddCommGroup N] [AddCommGroup P] [Module B N] [Module B P]

/-- An ordinary linear map, as an intertwiner of the adapted original actions. -/
def nonUnitalHom (f : M →ₗ[B] N) :
    @NonUnitalModuleHom B M N _ _ _ (NonUnitalModule.ofModule B M)
      (NonUnitalModule.ofModule B N) := by
  letI := NonUnitalModule.ofModule B M
  letI := NonUnitalModule.ofModule B N
  exact
    { toAddMonoidHom := f.toAddMonoidHom
      map_smul' := f.map_smul }

theorem nonUnitalHom_toAddMonoidHom (f : M →ₗ[B] N) :
    letI := NonUnitalModule.ofModule B M
    letI := NonUnitalModule.ofModule B N
    (nonUnitalHom f).toAddMonoidHom = f.toAddMonoidHom := rfl

/-- The published residual-action intertwiner of the original tensor map. -/
def residualMap (f : M →ₗ[B] N) :
    @NonUnitalModuleHom A (Tensor φ M) (Tensor φ N) _ _ _ (residualModule φ M)
      (residualModule φ N) := by
  letI := rightModule φ
  letI := NonUnitalModule.regular A
  letI := NonUnitalModule.ofModule B M
  letI := NonUnitalModule.ofModule B N
  exact NonUnitalBimoduleTensor.leftMap (actionsCommute φ) (actionsCommute φ)
    (NonUnitalBimoduleHom.id A B A) (nonUnitalHom f)

/-- Its whole additive map is the published original-action tensor map. -/
theorem residualMap_toAddMonoidHom (f : M →ₗ[B] N) :
    letI := rightModule φ
    letI := NonUnitalModule.regular A
    letI := NonUnitalModule.ofModule B M
    letI := NonUnitalModule.ofModule B N
    letI := residualModule φ M
    letI := residualModule φ N
    (residualMap φ f).toAddMonoidHom =
      NonUnitalModuleTensor.map B (NonUnitalBimoduleHom.id A B A).toRightHom
        (nonUnitalHom f) := rfl

/-- The residual intertwining law. -/
theorem residualMap_smul (f : M →ₗ[B] N) (a : A) (t : Tensor φ M) :
    letI := residualModule φ M
    letI := residualModule φ N
    residualMap φ f (a • t) = a • residualMap φ f t := by
  let _ := residualModule φ M
  let _ := residualModule φ N
  exact NonUnitalModuleHom.map_smul _ a t

/-- The actual tensor map, upgraded from the published residual-action intertwiner. -/
def tensorMap (f : M →ₗ[B] N) : tensorObj φ M →ₗ[A] tensorObj φ N := by
  letI := residualModule φ M
  letI := residualModule φ N
  exact
    { toAddHom := (residualMap φ f).toAddMonoidHom.toAddHom
      map_smul' := residualMap_smul φ f }

theorem tensorMap_toAddMonoidHom (f : M →ₗ[B] N) :
    letI := residualModule φ M
    letI := residualModule φ N
    (tensorMap φ f).toAddMonoidHom = (residualMap φ f).toAddMonoidHom := rfl

@[simp] theorem tensorMap_tmul (f : M →ₗ[B] N) (a : A) (m : M) :
    tensorMap φ f (tmul φ M a m) = tmul φ N a (f m) := rfl

theorem tensorMap_id :
    tensorMap φ (LinearMap.id : M →ₗ[B] M) =
      (LinearMap.id : tensorObj φ M →ₗ[A] tensorObj φ M) :=
  hom_ext φ M fun _ _ => rfl

theorem tensorMap_comp (g : N →ₗ[B] P) (f : M →ₗ[B] N) :
    tensorMap φ (g.comp f) = (tensorMap φ g).comp (tensorMap φ f) :=
  hom_ext φ M fun _ _ => rfl

/-- Extension on a common carrier universe closed under tensoring with A. -/
def functor :
    ModuleCat.{max uA uM} B ⥤ ModuleCat.{max uA uM} A where
  obj M := tensorObj φ M
  map {M N} f := ModuleCat.ofHom (X := tensorObj φ M) (Y := tensorObj φ N)
    (tensorMap φ f.hom)
  map_id _ := ModuleCat.hom_ext (tensorMap_id φ)
  map_comp f g := ModuleCat.hom_ext (tensorMap_comp φ g.hom f.hom)

theorem functor_obj (M : ModuleCat.{max uA uM} B) : (functor φ).obj M = tensorObj φ M := rfl

theorem functor_obj_carrier (M : ModuleCat.{max uA uM} B) :
    ((functor φ).obj M).carrier = Tensor φ M := rfl

theorem functor_map_hom {M N : ModuleCat.{max uA uM} B} (f : M ⟶ N) :
    ((functor φ).map f).hom = tensorMap φ f.hom := rfl

theorem functor_map_tmul {M N : ModuleCat.{max uA uM} B} (f : M ⟶ N) (a : A) (m : M) :
    ((functor φ).map f).hom (tmul φ M a m) = tmul φ N a (f.hom m) := rfl

/-- Native ordinary restriction, with the action pulled back through the same φ. -/
abbrev restriction : ModuleCat.{uM} A ⥤ ModuleCat.{uM} B :=
  ModuleCat.restrictScalars φ

theorem restriction_obj_carrier (M : ModuleCat.{uM} A) :
    ((restriction φ).obj M).carrier = M.carrier := rfl

theorem restriction_obj_isModule (M : ModuleCat.{uM} A) :
    ((restriction φ).obj M).isModule = Module.compHom M φ := rfl

theorem restriction_smul (M : ModuleCat.{uM} A) (b : B) (m : (restriction φ).obj M) :
    b • m = φ b • (show M from m) := rfl

theorem restriction_map_function {M N : ModuleCat.{uM} A} (f : M ⟶ N) :
    (((restriction φ).map f).hom : M → N) = f.hom := rfl

theorem restriction_map {M N : ModuleCat.{uM} A} (f : M ⟶ N) (m : M) :
    ((restriction φ).map f).hom m = f.hom m := rfl

section Subalgebra

variable {k : Type uk} [CommRing k] [Algebra k A] (S : Subalgebra k A)

/-- The source subalgebra example, retaining a possibly noncommutative A. -/
abbrev subalgebraFunctor :
    ModuleCat.{max uA uM} S ⥤ ModuleCat.{max uA uM} A :=
  functor S.val.toRingHom

abbrev subalgebraRestriction : ModuleCat.{uM} A ⥤ ModuleCat.{uM} S :=
  restriction S.val.toRingHom

/-- Coefficients are transported through the actual subalgebra inclusion. -/
theorem coefficient_balanced (M : Type uM) [AddCommGroup M] [Module S M]
    (c : k) (a : A) (m : M) :
    letI := module S.val.toRingHom M
    algebraMap k A c • tmul S.val.toRingHom M a m =
        tmul S.val.toRingHom M a ((algebraMap k S c) • m) := by
  let _ := module S.val.toRingHom M
  rw [smul_tmul, Algebra.commutes c a]
  have hc : S.val.toRingHom (algebraMap k S c) = algebraMap k A c := S.val.commutes c
  simpa only [hc] using
    tmul_balanced S.val.toRingHom M (algebraMap k S c) a m

end Subalgebra

/-! Development checks: independent levels, a noninjective homomorphism and a
noncommutative algebra. -/

example {B : Type 2} {A : Type} [Ring B] [Ring A] (φ : B →+* A) :
    ModuleCat.{1} B ⥤ ModuleCat.{1} A := functor.{2, 0, 1} φ

example {B : Type} {A : Type 1} [Ring B] [Ring A] (φ : B →+* A) :
    ModuleCat.{1} B ⥤ ModuleCat.{1} A := functor.{0, 1, 0} φ

example {B : Type 1} {A : Type} [Ring B] [Ring A] (φ : B →+* A)
    {M : Type 2} {N : Type} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (f : M →ₗ[B] N) : tensorObj.{1, 0, 2} φ M →ₗ[A] tensorObj.{1, 0, 0} φ N :=
  tensorMap φ f

example {B : Type 1} {A : Type} [Ring B] [Ring A] (φ : B →+* A) :
    ModuleCat.{2} A ⥤ ModuleCat.{2} B := restriction.{1, 0, 2} φ

example : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} PUnit := functor (Int.castRingHom PUnit)

example (S : Subalgebra ℤ (Module.End ℤ (ℤ × ℤ))) :
    ModuleCat.{0} S ⥤ ModuleCat.{0} (Module.End ℤ (ℤ × ℤ)) :=
  subalgebraFunctor S

end Langlands.Algebra.UnitalScalarExtension
