import Langlands.Algebra.NonUnitalModuleCornerInduction
import Mathlib.Algebra.Module.PUnit

/-!
# Interface and boundary checks for actual additive corner induction

These internal checks retain the named original actions and independent
universes. See the same-stem Markdown for source correspondence and scope.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleCornerInductionChecks

open CategoryTheory MulOpposite
open Langlands.Algebra.NonUnitalModuleCornerInduction

universe uA uZ uZ' uZ''

attribute [local instance] rightCornerModule cornerModule tensorModule

/-! Complete, unapplied declaration types. -/

section Interfaces

set_option linter.unusedVariables false

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    NonUnitalModule (Idempotent.Corner e)ᵐᵒᵖ A := @rightCornerModule

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (c : (Idempotent.Corner e)ᵐᵒᵖ) (a : A),
    (rightCornerModule e).toDistribSMul.toSMul.smul c a =
      a * Idempotent.Corner.toAmbient e c.unop := @rightCornerModule_smul

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (c : (Idempotent.Corner e)ᵐᵒᵖ),
    NonUnitalModule.toEndHom (rightCornerModule e) c =
      { toFun := fun a => a * Idempotent.Corner.toAmbient e c.unop
        map_zero' := zero_mul _
        map_add' := fun a b => add_mul a b _ } := @toEndHom_rightCornerModule

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    @ActionsCommute A (Idempotent.Corner e) A _ _ _
      (NonUnitalModule.regular A) (rightCornerModule e) := @regularCornerCommute

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    NonUnitalModule (Idempotent.Corner e) Z := @cornerModule

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    Type (max uA uZ) := @Tensor

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    AddCommGroup (Tensor e Z) := @tensorAddCommGroup

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    tensorAddCommGroup e Z =
      NonUnitalModuleTensor.addCommGroup (Idempotent.Corner e) A Z :=
  @tensorAddCommGroup_def

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    @NonUnitalModule A (Tensor e Z) _ (tensorAddCommGroup e Z) := @tensorModule

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    letI := NonUnitalModule.regular A
    tensorModule e Z = NonUnitalBimoduleTensor.leftModule (regularCornerCommute e) Z :=
  @tensorModule_def

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    A → Z → Tensor e Z := @tmul

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} [AddCommGroup Z] [Module (Idempotent.Corner e) Z]
    (a₀ a : A) (z : Z),
    (tensorModule e Z).toDistribSMul.toSMul.smul a₀ (tmul e a z) =
      tmul e (a₀ * a) z := @tensorModule_smul_tmul

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} [AddCommGroup Z] [Module (Idempotent.Corner e) Z]
    (c : Idempotent.Corner e) (a : A) (z : Z),
    tmul e (a * Idempotent.Corner.toAmbient e c) z = tmul e a (c • z) :=
  @tmul_balanced

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z] (a₀ : A),
    letI := NonUnitalModule.regular A
    NonUnitalModule.toEndHom (tensorModule e Z) a₀ =
      NonUnitalModuleTensor.map (Idempotent.Corner e)
        ((regularCornerCommute e).leftActionHom a₀)
        (NonUnitalModuleHom.id (Idempotent.Corner e) Z) := @toEndHom_tensorModule

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} {Z' : Type uZ'} [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z'],
    (Z →ₗ[Idempotent.Corner e] Z') →
      @NonUnitalModuleHom (Idempotent.Corner e) Z Z' _ _ _
        (cornerModule e Z) (cornerModule e Z') := @originalMap

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} {Z' : Type uZ'} [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
    (f : Z →ₗ[Idempotent.Corner e] Z'),
    (originalMap e f).toAddMonoidHom = f.toAddMonoidHom :=
  @originalMap_toAddMonoidHom

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} {Z' : Type uZ'} [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z'],
    (Z →ₗ[Idempotent.Corner e] Z') →
      @NonUnitalModuleHom A (Tensor e Z) (Tensor e Z') _ _ _
        (tensorModule e Z) (tensorModule e Z') := @inducedMap

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} {Z' : Type uZ'} [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
    (f : Z →ₗ[Idempotent.Corner e] Z'),
    (inducedMap e f).toAddMonoidHom =
      NonUnitalModuleTensor.map (Idempotent.Corner e)
        (NonUnitalModuleHom.id (Idempotent.Corner e)ᵐᵒᵖ A) (originalMap e f) :=
  @inducedMap_toAddMonoidHom

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} {Z' : Type uZ'} [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
    (f : Z →ₗ[Idempotent.Corner e] Z') (a : A) (z : Z),
    inducedMap e f (tmul e a z) = tmul e a (f z) := @inducedMap_tmul

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} {Z' : Type uZ'} [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
    {f g : @NonUnitalModuleHom A (Tensor e Z) (Tensor e Z') _ _ _
      (tensorModule e Z) (tensorModule e Z')},
    (∀ a z, f (tmul e a z) = g (tmul e a z)) → f = g := @induced_hom_ext

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    inducedMap e (LinearMap.id : Z →ₗ[Idempotent.Corner e] Z) =
      @NonUnitalModuleHom.id A (Tensor e Z) _ _ (tensorModule e Z) := @inducedMap_id

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} {Z' : Type uZ'} {Z'' : Type uZ''}
    [AddCommGroup Z] [AddCommGroup Z'] [AddCommGroup Z'']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
    [Module (Idempotent.Corner e) Z'']
    (g : Z' →ₗ[Idempotent.Corner e] Z'') (f : Z →ₗ[Idempotent.Corner e] Z'),
    inducedMap e (g.comp f) = (inducedMap e g).comp (inducedMap e f) := @inducedMap_comp

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} {Z' : Type uZ'} [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z'],
    inducedMap e (0 : Z →ₗ[Idempotent.Corner e] Z') = 0 := @inducedMap_zero

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} {Z' : Type uZ'} [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
    (f g : Z →ₗ[Idempotent.Corner e] Z'),
    inducedMap e (f + g) = inducedMap e f + inducedMap e g := @inducedMap_add

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} {Z' : Type uZ'} [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z'],
    (Z →ₗ[Idempotent.Corner e] Z') →+
      @NonUnitalModuleHom A (Tensor e Z) (Tensor e Z') _ _ _
        (tensorModule e Z) (tensorModule e Z') := @inducedMapAddHom

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type uZ} {Z' : Type uZ'} [AddCommGroup Z] [AddCommGroup Z']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z'],
    ⇑(inducedMapAddHom (Z := Z) (Z' := Z') e) = inducedMap e := @coe_inducedMapAddHom

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    NonUnitalModuleCat.{uA, max uA uZ} A := @ambientObject

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    (ambientObject e Z).carrier = Tensor e Z := @ambientObject_carrier

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    (ambientObject e Z).isAddCommGroup = tensorAddCommGroup e Z := @ambientObject_isAddCommGroup

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    (ambientObject e Z).isModule = tensorModule e Z := @ambientObject_isModule

/-- A named complete declaration assignment, used as the companion's entry declaration. -/
def ambientFunctorInterface : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    ModuleCat.{uZ} (Idempotent.Corner e) ⥤ NonUnitalModuleCat.{uA, max uA uZ} A :=
  @ambientFunctor

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z : ModuleCat.{uZ} (Idempotent.Corner e)),
    (ambientFunctor e).obj Z = ambientObject e Z := @ambientFunctor_obj

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f : Z ⟶ Z'),
    (ambientFunctor e).map f = inducedMap e f.hom := @ambientFunctor_map

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f : Z ⟶ Z'),
    ((ambientFunctor e).map f).toAddMonoidHom =
      NonUnitalModuleTensor.map (Idempotent.Corner e)
        (NonUnitalModuleHom.id (Idempotent.Corner e)ᵐᵒᵖ A) (originalMap e f.hom) :=
  @ambientFunctor_map_toAddMonoidHom

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    (ambientFunctor.{uA, uZ} e).Additive := @ambientFunctor_additive

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)),
    (ambientFunctor e).map (0 : Z ⟶ Z') = 0 := @ambientFunctor_map_zero

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f g : Z ⟶ Z'),
    (ambientFunctor e).map (f + g) = (ambientFunctor e).map f + (ambientFunctor e).map g :=
  @ambientFunctor_map_add

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    @IsNondegenerate A (Tensor e Z) _ (tensorAddCommGroup e Z) (tensorModule e Z) :=
  @isNondegenerate

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    NondegenerateModuleCat.{uA, max uA uZ} A := @nondegenerateObject

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    (nondegenerateObject hA e Z).obj = ambientObject e Z := @nondegenerateObject_obj

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    ModuleCat.{uZ} (Idempotent.Corner e) ⥤ NondegenerateModuleCat.{uA, max uA uZ} A :=
  @nondegenerateFunctor

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (Z : ModuleCat.{uZ} (Idempotent.Corner e)),
    (nondegenerateFunctor hA e).obj Z = nondegenerateObject hA e Z :=
  @nondegenerateFunctor_obj

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (Z : ModuleCat.{uZ} (Idempotent.Corner e)),
    ((nondegenerateFunctor hA e).obj Z).obj.isModule = tensorModule e Z :=
  @nondegenerateFunctor_obj_isModule

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f : Z ⟶ Z'),
    ((nondegenerateFunctor hA e).map f).hom = inducedMap e f.hom :=
  @nondegenerateFunctor_map_hom

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f : Z ⟶ Z'),
    ((nondegenerateFunctor hA e).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map (Idempotent.Corner e)
        (NonUnitalModuleHom.id (Idempotent.Corner e)ᵐᵒᵖ A) (originalMap e f.hom) :=
  @nondegenerateFunctor_map_toAddMonoidHom

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    (nondegenerateFunctor.{uA, uZ} hA e).Additive := @nondegenerateFunctor_additive

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)),
    (nondegenerateFunctor hA e).map (0 : Z ⟶ Z') = 0 := @nondegenerateFunctor_map_zero

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f g : Z ⟶ Z'),
    (nondegenerateFunctor hA e).map (f + g) =
      (nondegenerateFunctor hA e).map f + (nondegenerateFunctor hA e).map g :=
  @nondegenerateFunctor_map_add

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    nondegenerateFunctor.{uA, uZ} hA e ⋙ nondegenerateInclusion A =
      ambientFunctor.{uA, uZ} e := @nondegenerateFunctor_comp_inclusion

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (Z : ModuleCat.{uZ} (Idempotent.Corner e)),
    ((nondegenerateFunctor hA e ⋙ nondegenerateInclusion A).obj Z).isModule =
      ((ambientFunctor e).obj Z).isModule := @inclusion_obj_isModule

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f : Z ⟶ Z'),
    (nondegenerateFunctor hA e ⋙ nondegenerateInclusion A).map f =
      (ambientFunctor e).map f := @inclusion_map

/-! Explicit unequal universe checks in both directions. -/

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type 1) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    Type 1 := @Tensor

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A)
    (Z : Type 0) [AddCommGroup Z] [Module (Idempotent.Corner e) Z],
    Type 1 := @Tensor

example : ∀ {A : Type 3} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type 2} {Z' : Type 1} {Z'' : Type 0}
    [AddCommGroup Z] [AddCommGroup Z'] [AddCommGroup Z'']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
    [Module (Idempotent.Corner e) Z'']
    (g : Z' →ₗ[Idempotent.Corner e] Z'') (f : Z →ₗ[Idempotent.Corner e] Z'),
    inducedMap e (g.comp f) = (inducedMap e g).comp (inducedMap e f) := @inducedMap_comp

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A)
    {Z : Type 1} {Z' : Type 2} {Z'' : Type 3}
    [AddCommGroup Z] [AddCommGroup Z'] [AddCommGroup Z'']
    [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
    [Module (Idempotent.Corner e) Z'']
    (g : Z' →ₗ[Idempotent.Corner e] Z'') (f : Z →ₗ[Idempotent.Corner e] Z'),
    inducedMap e (g.comp f) = (inducedMap e g).comp (inducedMap e f) := @inducedMap_comp

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
    ModuleCat.{1} (Idempotent.Corner e) ⥤ NonUnitalModuleCat.{0, 1} A := @ambientFunctor

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
    ModuleCat.{0} (Idempotent.Corner e) ⥤ NonUnitalModuleCat.{1, 1} A := @ambientFunctor

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    ModuleCat.{1} (Idempotent.Corner e) ⥤ NondegenerateModuleCat.{0, 1} A :=
  @nondegenerateFunctor

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    ModuleCat.{0} (Idempotent.Corner e) ⥤ NondegenerateModuleCat.{1, 1} A :=
  @nondegenerateFunctor

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    nondegenerateFunctor.{0, 1} hA e ⋙ nondegenerateInclusion A =
      ambientFunctor.{0, 1} e := @nondegenerateFunctor_comp_inclusion

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    nondegenerateFunctor.{1, 0} hA e ⋙ nondegenerateInclusion A =
      ambientFunctor.{1, 0} e := @nondegenerateFunctor_comp_inclusion

end Interfaces

section CompetingActions

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
-- The overlaps are deliberate inputs to the structure-selection checks.
set_option linter.overlappingInstances false

variable {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
  {Z : Type uZ} {Z' : Type uZ'} [AddCommGroup Z] [AddCommGroup Z']
  [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
  [otherLeft : NonUnitalModule A A]
  [otherRight : NonUnitalModule (Idempotent.Corner e)ᵐᵒᵖ A]
  [otherCorner : NonUnitalModule (Idempotent.Corner e) Z]
  [otherCorner' : NonUnitalModule (Idempotent.Corner e) Z']
  [otherTensor : NonUnitalModule A (Tensor e Z)]
  [otherTensor' : NonUnitalModule A (Tensor e Z')]

include otherLeft otherRight otherCorner otherCorner' otherTensor otherTensor'

example : (inferInstance : NonUnitalModule A A) = otherLeft := rfl
example : (inferInstance : NonUnitalModule (Idempotent.Corner e)ᵐᵒᵖ A) = otherRight := rfl
example : (inferInstance : NonUnitalModule (Idempotent.Corner e) Z) = otherCorner := rfl
example : (inferInstance : NonUnitalModule A (Tensor e Z)) = otherTensor := rfl

example : Tensor e Z =
    @NonUnitalModuleTensor.Tensor (Idempotent.Corner e) A Z _ _ _
      (rightCornerModule e) (cornerModule e Z) := rfl

example : tensorAddCommGroup e Z =
    @NonUnitalModuleTensor.addCommGroup (Idempotent.Corner e) A Z _ _ _
      (rightCornerModule e) (cornerModule e Z) := rfl

example : @ActionsCommute A (Idempotent.Corner e) A _ _ _
    (NonUnitalModule.regular A) (rightCornerModule e) := regularCornerCommute e

example :
    letI := NonUnitalModule.regular A
    letI := rightCornerModule e
    letI := cornerModule e Z
    tensorModule e Z = NonUnitalBimoduleTensor.leftModule (regularCornerCommute e) Z := rfl

example (f : Z →ₗ[Idempotent.Corner e] Z') :
    @NonUnitalModuleHom A (Tensor e Z) (Tensor e Z') _ _ _
      (tensorModule e Z) (tensorModule e Z') := inducedMap e f

example (f : Z →ₗ[Idempotent.Corner e] Z') :
    letI := rightCornerModule e
    letI := cornerModule e Z
    letI := cornerModule e Z'
    @NonUnitalModuleHom.toAddMonoidHom A (Tensor e Z) (Tensor e Z') _ _ _
        (tensorModule e Z) (tensorModule e Z') (inducedMap e f) =
      NonUnitalModuleTensor.map (Idempotent.Corner e)
        (NonUnitalModuleHom.id (Idempotent.Corner e)ᵐᵒᵖ A) (originalMap e f) := rfl

example (hA : IsIdempotented A) :
    @IsNondegenerate A (Tensor e Z) _ (tensorAddCommGroup e Z) (tensorModule e Z) :=
  isNondegenerate hA e Z

example : (ambientObject e Z).isModule = tensorModule e Z := rfl

end CompetingActions

section CompetingRingsAndGroups

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
-- Every competing structure is intentional; the original arguments stay explicit.
set_option linter.overlappingInstances false

variable (A : Type uA) (a₀ : NonUnitalRing A) [a₁ : NonUnitalRing A]
  (e : letI := a₀; Idempotent A)
  (Z : Type uZ) (Z' : Type uZ')
  (gz₀ : AddCommGroup Z) [gz₁ : AddCommGroup Z]
  (gz'₀ : AddCommGroup Z') [gz'₁ : AddCommGroup Z']

local notation "C₀" => @Idempotent.Corner A a₀ e
local notation "c₀" => @Idempotent.Corner.ring A a₀ e

variable (mz₀ : letI := a₀; letI := gz₀; Module (Idempotent.Corner e) Z)
  (mz'₀ : letI := a₀; letI := gz'₀; Module (Idempotent.Corner e) Z')
  [c₁ : Ring (@Idempotent.Corner A a₀ e)]
  [mz₁ : @Module (@Idempotent.Corner A a₀ e) Z c₁.toSemiring gz₁.toAddCommMonoid]
  [mz'₁ : @Module (@Idempotent.Corner A a₀ e) Z' c₁.toSemiring gz'₁.toAddCommMonoid]

local notation "Q₀" => @Tensor A a₀ e Z gz₀ mz₀
local notation "Q'₀" => @Tensor A a₀ e Z' gz'₀ mz'₀
local notation "gq₀" => @tensorAddCommGroup A a₀ e Z gz₀ mz₀
local notation "gq'₀" => @tensorAddCommGroup A a₀ e Z' gz'₀ mz'₀
local notation "mq₀" => @tensorModule A a₀ e Z gz₀ mz₀
local notation "mq'₀" => @tensorModule A a₀ e Z' gz'₀ mz'₀

variable [gq₁ : AddCommGroup (@Tensor A a₀ e Z gz₀ mz₀)]
  [gq'₁ : AddCommGroup (@Tensor A a₀ e Z' gz'₀ mz'₀)]
  [mq₁ : NonUnitalModule A (@Tensor A a₀ e Z gz₀ mz₀)]
  [mq'₁ : NonUnitalModule A (@Tensor A a₀ e Z' gz'₀ mz'₀)]

include a₁ gz₁ gz'₁ c₁ mz₁ mz'₁ gq₁ gq'₁ mq₁ mq'₁

example : (inferInstance : NonUnitalRing A) = a₁ := rfl
example : (inferInstance : Ring C₀) = c₁ := rfl
example : (inferInstance : AddCommGroup Z) = gz₁ := rfl
example : (inferInstance : AddCommGroup Z') = gz'₁ := rfl
example : (inferInstance : @Module C₀ Z c₁.toSemiring gz₁.toAddCommMonoid) = mz₁ := rfl
example : (inferInstance : @Module C₀ Z' c₁.toSemiring gz'₁.toAddCommMonoid) = mz'₁ := rfl
example : (inferInstance : AddCommGroup Q₀) = gq₁ := rfl
example : (inferInstance : AddCommGroup Q'₀) = gq'₁ := rfl
example : (inferInstance : NonUnitalModule A Q₀) = mq₁ := rfl
example : (inferInstance : NonUnitalModule A Q'₀) = mq'₁ := rfl

example :
    Q₀ = @NonUnitalModuleTensor.Tensor C₀ A Z (c₀).toNonUnitalRing
      a₀.toAddCommGroup gz₀ (@rightCornerModule A a₀ e)
      (@cornerModule A a₀ e Z gz₀ mz₀) := rfl

example :
    gq₀ = @NonUnitalModuleTensor.addCommGroup C₀ A Z (c₀).toNonUnitalRing
      a₀.toAddCommGroup gz₀ (@rightCornerModule A a₀ e)
      (@cornerModule A a₀ e Z gz₀ mz₀) := rfl

example :
    @ActionsCommute A C₀ A a₀ (c₀).toNonUnitalRing a₀.toAddCommGroup
      (@NonUnitalModule.regular A a₀) (@rightCornerModule A a₀ e) :=
  @regularCornerCommute A a₀ e

example :
    mq₀ = @NonUnitalBimoduleTensor.leftModule A C₀ a₀ (c₀).toNonUnitalRing
      A a₀.toAddCommGroup (@NonUnitalModule.regular A a₀)
      (@rightCornerModule A a₀ e) (@regularCornerCommute A a₀ e)
      Z gz₀ (@cornerModule A a₀ e Z gz₀ mz₀) := rfl

example (f : @LinearMap C₀ C₀ (c₀).toSemiring (c₀).toSemiring
    (@RingHom.id C₀ (c₀).toNonAssocSemiring) Z Z'
    gz₀.toAddCommMonoid gz'₀.toAddCommMonoid mz₀ mz'₀) :
    @NonUnitalModuleHom A Q₀ Q'₀ a₀ gq₀ gq'₀ mq₀ mq'₀ :=
  @inducedMap A a₀ e Z Z' gz₀ gz'₀ mz₀ mz'₀ f

example (hA : @IsIdempotented A a₀) :
    @IsNondegenerate A Q₀ a₀ gq₀ mq₀ :=
  @isNondegenerate A a₀ hA e Z gz₀ mz₀

example :
    @ambientObject A a₀ e Z gz₀ mz₀ = @NonUnitalModuleCat.of A a₀ Q₀ gq₀ mq₀ := rfl

example :
    @NonUnitalModuleCat.isAddCommGroup A a₀ (@ambientObject A a₀ e Z gz₀ mz₀) = gq₀ := rfl

example :
    @NonUnitalModuleCat.isModule A a₀ (@ambientObject A a₀ e Z gz₀ mz₀) = mq₀ := rfl

end CompetingRingsAndGroups

section BoundaryCases

variable {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
  (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z]

example [Subsingleton Z] : Subsingleton (Tensor e Z) := by
  have h : AddMonoidHom.id (Tensor e Z) = 0 :=
    NonUnitalModuleTensor.hom_ext (Idempotent.Corner e) fun a z => by
      change tmul e a z = 0
      rw [Subsingleton.elim z 0]
      exact NonUnitalModuleTensor.tmul_zero _ _ _ a
  exact ⟨fun s t => (DFunLike.congr_fun h s).trans (DFunLike.congr_fun h t).symm⟩

example [Subsingleton A] : Subsingleton (Tensor e Z) := by
  have h : AddMonoidHom.id (Tensor e Z) = 0 :=
    NonUnitalModuleTensor.hom_ext (Idempotent.Corner e) fun a z => by
      change tmul e a z = 0
      rw [Subsingleton.elim a 0]
      exact NonUnitalModuleTensor.zero_tmul _ _ _ z
  exact ⟨fun s t => (DFunLike.congr_fun h s).trans (DFunLike.congr_fun h t).symm⟩

example (he : (e : A) = 0) : Subsingleton (Tensor e Z) := by
  have h : AddMonoidHom.id (Tensor e Z) = 0 :=
    NonUnitalModuleTensor.hom_ext (Idempotent.Corner e) fun a z => by
      change tmul e a z = 0
      have hbal := tmul_balanced e (1 : Idempotent.Corner e) a z
      rw [Idempotent.Corner.toAmbient_one, he, mul_zero, one_smul] at hbal
      exact hbal.symm.trans (NonUnitalModuleTensor.zero_tmul _ _ _ z)
  exact ⟨fun s t => (DFunLike.congr_fun h s).trans (DFunLike.congr_fun h t).symm⟩

example (hA : IsIdempotented A) :
    @IsNondegenerate A (Tensor e PUnit.{uZ + 1}) _ (tensorAddCommGroup e PUnit)
      (tensorModule e PUnit) := isNondegenerate hA e PUnit

example :
    let e₀ : Idempotent ℤ := ⟨0, IsIdempotentElem.zero⟩
    (rightCornerModule e₀).toDistribSMul.toSMul.smul (op (1 : Idempotent.Corner e₀)) 1 ≠ 1 := by
  change (0 : ℤ) ≠ 1
  exact zero_ne_one

example :
    let e₀ : Idempotent PUnit.{uA + 1} := ⟨0, IsIdempotentElem.zero⟩
    @IsNondegenerate PUnit (Tensor e₀ PUnit.{uZ + 1}) _
      (tensorAddCommGroup e₀ PUnit) (tensorModule e₀ PUnit) :=
  isNondegenerate (IsIdempotented.of_ring PUnit) ⟨0, IsIdempotentElem.zero⟩ PUnit

end BoundaryCases

end Langlands.Algebra.NonUnitalModuleCornerInductionChecks
