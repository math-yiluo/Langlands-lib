import Langlands.Algebra.NonUnitalBimoduleTensor
import Langlands.Algebra.NonUnitalModuleCorner

/-!
# The actual additive corner-induction construction

Renard (9 July 2026), I.3.2, printed p.20/PDF26. The right corner action
on the ambient ring is retained without a unit law. This is the arbitrary-ring
additive foundation; comparison of complex scalar structures is separate.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCornerInduction

open CategoryTheory MulOpposite
open scoped TensorProduct

universe uA uZ uZ' uZ''

variable {A : Type uA} [NonUnitalRing A]

/-- The original right corner action, with no unit-law assertion. -/
@[instance_reducible] def rightCornerModule (e : Idempotent A) :
    NonUnitalModule (Idempotent.Corner e)ᵐᵒᵖ A where
  smul c a := a * Idempotent.Corner.toAmbient e c.unop
  smul_zero c := zero_mul _
  smul_add c a b := add_mul a b _
  mul_smul c d a := by
    change a * Idempotent.Corner.toAmbient e (d.unop * c.unop) =
      (a * Idempotent.Corner.toAmbient e d.unop) * Idempotent.Corner.toAmbient e c.unop
    rw [map_mul, mul_assoc]
  add_smul c d a := by
    change a * Idempotent.Corner.toAmbient e (c.unop + d.unop) =
      a * Idempotent.Corner.toAmbient e c.unop + a * Idempotent.Corner.toAmbient e d.unop
    rw [map_add, mul_add]
  zero_smul a := by
    change a * Idempotent.Corner.toAmbient e 0 = 0
    rw [map_zero, mul_zero]

attribute [local instance] rightCornerModule

theorem rightCornerModule_smul (e : Idempotent A) (c : (Idempotent.Corner e)ᵐᵒᵖ) (a : A) :
    (rightCornerModule e).toDistribSMul.toSMul.smul c a =
      a * Idempotent.Corner.toAmbient e c.unop := rfl

/-- The entire scalar endomorphism, on the original additive group of `A`. -/
theorem toEndHom_rightCornerModule (e : Idempotent A) (c : (Idempotent.Corner e)ᵐᵒᵖ) :
    NonUnitalModule.toEndHom (rightCornerModule e) c =
      { toFun := fun a => a * Idempotent.Corner.toAmbient e c.unop
        map_zero' := zero_mul _
        map_add' := fun a b => add_mul a b _ } := rfl

/-- Original left multiplication commutes with original right corner multiplication. -/
theorem regularCornerCommute (e : Idempotent A) :
    @ActionsCommute A (Idempotent.Corner e) A _ _ _
      (NonUnitalModule.regular A) (rightCornerModule e) :=
  fun a c b => (mul_assoc a b (Idempotent.Corner.toAmbient e c)).symm

/-- The chosen original left corner action is exactly the ordinary-module adapter. -/
abbrev cornerModule (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] : NonUnitalModule (Idempotent.Corner e) Z :=
  NonUnitalModule.ofModule (Idempotent.Corner e) Z

attribute [local instance] cornerModule

/-- The actual published balanced quotient with the two explicitly selected actions. -/
abbrev Tensor (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] : Type (max uA uZ) :=
  @NonUnitalModuleTensor.Tensor (Idempotent.Corner e) A Z _ _ _
    (rightCornerModule e) (cornerModule e Z)

/-- The inherited additive group of the actual balanced quotient. -/
abbrev tensorAddCommGroup (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] : AddCommGroup (Tensor e Z) :=
  @NonUnitalModuleTensor.addCommGroup (Idempotent.Corner e) A Z _ _ _
    (rightCornerModule e) (cornerModule e Z)

theorem tensorAddCommGroup_def (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] :
    tensorAddCommGroup e Z =
      NonUnitalModuleTensor.addCommGroup (Idempotent.Corner e) A Z := rfl

/-- The named residual original `A`-action, using the published left tensor action. -/
@[instance_reducible] def tensorModule (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] : NonUnitalModule A (Tensor e Z) := by
  letI := NonUnitalModule.regular A
  letI := rightCornerModule e
  letI := cornerModule e Z
  exact NonUnitalBimoduleTensor.leftModule (regularCornerCommute e) Z

attribute [local instance] tensorModule

theorem tensorModule_def (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] :
    letI := NonUnitalModule.regular A
    tensorModule e Z = NonUnitalBimoduleTensor.leftModule (regularCornerCommute e) Z := rfl

/-- Pure tensors in the actual quotient. -/
def tmul (e : Idempotent A) {Z : Type uZ} [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] (a : A) (z : Z) : Tensor e Z :=
  @NonUnitalModuleTensor.tmul (Idempotent.Corner e) A Z _ _ _
    (rightCornerModule e) (cornerModule e Z) a z

theorem tensorModule_smul_tmul (e : Idempotent A) {Z : Type uZ} [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] (a₀ a : A) (z : Z) :
    (tensorModule e Z).toDistribSMul.toSMul.smul a₀ (tmul e a z) =
      tmul e (a₀ * a) z := rfl

theorem tmul_balanced (e : Idempotent A) {Z : Type uZ} [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] (c : Idempotent.Corner e) (a : A) (z : Z) :
    tmul e (a * Idempotent.Corner.toAmbient e c) z = tmul e a (c • z) := by
  exact NonUnitalModuleTensor.tmul_balanced (Idempotent.Corner e) A Z c a z

/-- The entire scalar endomorphism is the published tensor map. -/
theorem toEndHom_tensorModule (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] (a₀ : A) :
    letI := NonUnitalModule.regular A
    NonUnitalModule.toEndHom (tensorModule e Z) a₀ =
      NonUnitalModuleTensor.map (Idempotent.Corner e)
        ((regularCornerCommute e).leftActionHom a₀)
        (NonUnitalModuleHom.id (Idempotent.Corner e) Z) := rfl

section Maps

variable (e : Idempotent A)
  {Z : Type uZ} {Z' : Type uZ'} {Z'' : Type uZ''}
  [AddCommGroup Z] [AddCommGroup Z'] [AddCommGroup Z'']
  [Module (Idempotent.Corner e) Z] [Module (Idempotent.Corner e) Z']
  [Module (Idempotent.Corner e) Z'']

/-- A whole corner-linear map under the explicit original-action adapters. -/
def originalMap (f : Z →ₗ[Idempotent.Corner e] Z') :
    @NonUnitalModuleHom (Idempotent.Corner e) Z Z' _ _ _
      (cornerModule e Z) (cornerModule e Z') where
  toAddMonoidHom := f.toAddMonoidHom
  map_smul' c z := f.map_smul c z

theorem originalMap_toAddMonoidHom (f : Z →ₗ[Idempotent.Corner e] Z') :
    (originalMap e f).toAddMonoidHom = f.toAddMonoidHom := rfl

/-- The actual original `A`-linear map `id ⊗ f`, with the named residual actions. -/
def inducedMap (f : Z →ₗ[Idempotent.Corner e] Z') :
    @NonUnitalModuleHom A (Tensor e Z) (Tensor e Z') _ _ _
      (tensorModule e Z) (tensorModule e Z') := by
  letI := NonUnitalModule.regular A
  letI := rightCornerModule e
  letI := cornerModule e Z
  letI := cornerModule e Z'
  exact NonUnitalBimoduleTensor.leftMap (regularCornerCommute e) (regularCornerCommute e)
    (NonUnitalBimoduleHom.id A (Idempotent.Corner e) A)
    (originalMap e f)

/-- The complete underlying additive map is the actual published tensor map. -/
theorem inducedMap_toAddMonoidHom (f : Z →ₗ[Idempotent.Corner e] Z') :
    (inducedMap e f).toAddMonoidHom =
      NonUnitalModuleTensor.map (Idempotent.Corner e)
        (NonUnitalModuleHom.id (Idempotent.Corner e)ᵐᵒᵖ A) (originalMap e f) := rfl

@[simp] theorem inducedMap_tmul (f : Z →ₗ[Idempotent.Corner e] Z') (a : A) (z : Z) :
    inducedMap e f (tmul e a z) = tmul e a (f z) := rfl

/-- Extensionality on pure tensors for whole original `A`-linear maps. -/
theorem induced_hom_ext
    {f g : @NonUnitalModuleHom A (Tensor e Z) (Tensor e Z') _ _ _
      (tensorModule e Z) (tensorModule e Z')}
    (h : ∀ a z, f (tmul e a z) = g (tmul e a z)) : f = g := by
  apply NonUnitalModuleHom.ext
  exact DFunLike.congr_fun (NonUnitalModuleTensor.hom_ext (Idempotent.Corner e) h)

theorem inducedMap_id :
    inducedMap e (LinearMap.id : Z →ₗ[Idempotent.Corner e] Z) =
      @NonUnitalModuleHom.id A (Tensor e Z) _ _ (tensorModule e Z) :=
  induced_hom_ext e (fun _ _ => rfl)

theorem inducedMap_comp (g : Z' →ₗ[Idempotent.Corner e] Z'')
    (f : Z →ₗ[Idempotent.Corner e] Z') :
    inducedMap e (g.comp f) = (inducedMap e g).comp (inducedMap e f) :=
  induced_hom_ext e (fun _ _ => rfl)

theorem inducedMap_zero :
    inducedMap e (0 : Z →ₗ[Idempotent.Corner e] Z') = 0 := by
  apply induced_hom_ext e
  intro a z
  exact NonUnitalModuleTensor.tmul_zero (Idempotent.Corner e) A Z' a

theorem inducedMap_add (f g : Z →ₗ[Idempotent.Corner e] Z') :
    inducedMap e (f + g) = inducedMap e f + inducedMap e g := by
  apply induced_hom_ext e
  intro a z
  exact NonUnitalModuleTensor.tmul_add (Idempotent.Corner e) A Z' a (f z) (g z)

/-- The actual map on the pointwise Hom groups is additive. -/
def inducedMapAddHom :
    (Z →ₗ[Idempotent.Corner e] Z') →+
      @NonUnitalModuleHom A (Tensor e Z) (Tensor e Z') _ _ _
        (tensorModule e Z) (tensorModule e Z') where
  toFun := inducedMap e
  map_zero' := inducedMap_zero e
  map_add' := inducedMap_add e

theorem coe_inducedMapAddHom :
    ⇑(inducedMapAddHom (Z := Z) (Z' := Z') e) = inducedMap e := rfl

end Maps

/-- The actual induced object, retaining exactly the quotient group and residual action. -/
def ambientObject (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] : NonUnitalModuleCat.{uA, max uA uZ} A :=
  @NonUnitalModuleCat.of A _ (Tensor e Z) (tensorAddCommGroup e Z) (tensorModule e Z)

theorem ambientObject_carrier (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] :
    (ambientObject e Z).carrier = Tensor e Z := rfl

theorem ambientObject_isAddCommGroup (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] :
    (ambientObject e Z).isAddCommGroup = tensorAddCommGroup e Z := rfl

theorem ambientObject_isModule (e : Idempotent A) (Z : Type uZ) [AddCommGroup Z]
    [Module (Idempotent.Corner e) Z] :
    (ambientObject e Z).isModule = tensorModule e Z := rfl

/-- Additive corner induction on all ordinary unital corner modules. -/
def ambientFunctor (e : Idempotent A) :
    ModuleCat.{uZ} (Idempotent.Corner e) ⥤ NonUnitalModuleCat.{uA, max uA uZ} A where
  obj Z := ambientObject e Z
  map f := inducedMap e f.hom
  map_id _ := inducedMap_id e
  map_comp f g := inducedMap_comp e g.hom f.hom

theorem ambientFunctor_obj (e : Idempotent A) (Z : ModuleCat.{uZ} (Idempotent.Corner e)) :
    (ambientFunctor e).obj Z = ambientObject e Z := rfl

theorem ambientFunctor_map (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f : Z ⟶ Z') :
    (ambientFunctor e).map f = inducedMap e f.hom := rfl

theorem ambientFunctor_map_toAddMonoidHom (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f : Z ⟶ Z') :
    ((ambientFunctor e).map f).toAddMonoidHom =
      NonUnitalModuleTensor.map (Idempotent.Corner e)
        (NonUnitalModuleHom.id (Idempotent.Corner e)ᵐᵒᵖ A) (originalMap e f.hom) := rfl

instance ambientFunctor_additive (e : Idempotent A) : (ambientFunctor.{uA, uZ} e).Additive where
  map_add := by
    intro Z Z' f g
    exact inducedMap_add e f.hom g.hom

@[simp] theorem ambientFunctor_map_zero (e : Idempotent A)
    (Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)) :
    (ambientFunctor e).map (0 : Z ⟶ Z') = 0 := (ambientFunctor e).map_zero Z Z'

@[simp] theorem ambientFunctor_map_add (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f g : Z ⟶ Z') :
    (ambientFunctor e).map (f + g) = (ambientFunctor e).map f + (ambientFunctor e).map g :=
  (ambientFunctor e).map_add

/-- Local units of the regular left factor fix every element of the actual quotient.
Contributed by Worker 1187. -/
theorem isNondegenerate (hA : IsIdempotented A) (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z] :
    @IsNondegenerate A (Tensor e Z) _ (tensorAddCommGroup e Z) (tensorModule e Z) := by
  classical
  let _ := rightCornerModule e
  let _ := cornerModule e Z
  let _ := tensorModule e Z
  intro t
  obtain ⟨q, rfl⟩ := NonUnitalModuleTensor.projection_surjective (Idempotent.Corner e) A Z t
  refine TensorProduct.inductionOn q ?_ ?_
  · intro a z
    obtain ⟨f, hf⟩ := hA.exists_mem_corner a
    refine ⟨f, ?_⟩
    change (tensorModule e Z).toDistribSMul.toSMul.smul (f : A) (tmul e a z) =
      tmul e a z
    rw [tensorModule_smul_tmul, ((Idempotent.mem_corner_iff f a).mp hf).1]
  · intro q r hq hr
    obtain ⟨f, hf⟩ := hq
    obtain ⟨g, hg⟩ := hr
    obtain ⟨k, hk⟩ := hA.finite_upper_bound {f, g}
    refine ⟨k, ?_⟩
    rw [map_add, smul_add, Idempotent.smul_eq_of_le (hk f (by simp)) hf,
      Idempotent.smul_eq_of_le (hk g (by simp)) hg]

/-- The identical original induced object, with intrinsic nondegeneracy attached. -/
def nondegenerateObject (hA : IsIdempotented A) (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z] :
    NondegenerateModuleCat.{uA, max uA uZ} A :=
  ⟨ambientObject e Z, isNondegenerate hA e Z⟩

theorem nondegenerateObject_obj (hA : IsIdempotented A) (e : Idempotent A)
    (Z : Type uZ) [AddCommGroup Z] [Module (Idempotent.Corner e) Z] :
    (nondegenerateObject hA e Z).obj = ambientObject e Z := rfl

/-- Additive corner induction into the actual full nondegenerate subcategory. -/
def nondegenerateFunctor (hA : IsIdempotented A) (e : Idempotent A) :
    ModuleCat.{uZ} (Idempotent.Corner e) ⥤ NondegenerateModuleCat.{uA, max uA uZ} A where
  obj Z := nondegenerateObject hA e Z
  map f := ObjectProperty.homMk (inducedMap e f.hom)
  map_id _ := by
    apply ObjectProperty.hom_ext
    exact inducedMap_id e
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact inducedMap_comp e g.hom f.hom

theorem nondegenerateFunctor_obj (hA : IsIdempotented A) (e : Idempotent A)
    (Z : ModuleCat.{uZ} (Idempotent.Corner e)) :
    (nondegenerateFunctor hA e).obj Z = nondegenerateObject hA e Z := rfl

theorem nondegenerateFunctor_obj_isModule (hA : IsIdempotented A) (e : Idempotent A)
    (Z : ModuleCat.{uZ} (Idempotent.Corner e)) :
    ((nondegenerateFunctor hA e).obj Z).obj.isModule = tensorModule e Z := rfl

theorem nondegenerateFunctor_map_hom (hA : IsIdempotented A) (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f : Z ⟶ Z') :
    ((nondegenerateFunctor hA e).map f).hom = inducedMap e f.hom := rfl

theorem nondegenerateFunctor_map_toAddMonoidHom (hA : IsIdempotented A) (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f : Z ⟶ Z') :
    ((nondegenerateFunctor hA e).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map (Idempotent.Corner e)
        (NonUnitalModuleHom.id (Idempotent.Corner e)ᵐᵒᵖ A) (originalMap e f.hom) := rfl

instance nondegenerateFunctor_additive (hA : IsIdempotented A) (e : Idempotent A) :
    (nondegenerateFunctor.{uA, uZ} hA e).Additive where
  map_add := by
    intro Z Z' f g
    apply ObjectProperty.hom_ext
    exact inducedMap_add e f.hom g.hom

@[simp] theorem nondegenerateFunctor_map_zero (hA : IsIdempotented A) (e : Idempotent A)
    (Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)) :
    (nondegenerateFunctor hA e).map (0 : Z ⟶ Z') = 0 :=
  (nondegenerateFunctor hA e).map_zero Z Z'

@[simp] theorem nondegenerateFunctor_map_add (hA : IsIdempotented A) (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f g : Z ⟶ Z') :
    (nondegenerateFunctor hA e).map (f + g) =
      (nondegenerateFunctor hA e).map f + (nondegenerateFunctor hA e).map g :=
  (nondegenerateFunctor hA e).map_add

/-- Inclusion agrees with the ambient functor as a whole functor, without transport. -/
theorem nondegenerateFunctor_comp_inclusion (hA : IsIdempotented A) (e : Idempotent A) :
    nondegenerateFunctor.{uA, uZ} hA e ⋙ nondegenerateInclusion A =
      ambientFunctor.{uA, uZ} e := rfl

/-- Equality of the original actions under inclusion. -/
theorem inclusion_obj_isModule (hA : IsIdempotented A) (e : Idempotent A)
    (Z : ModuleCat.{uZ} (Idempotent.Corner e)) :
    ((nondegenerateFunctor hA e ⋙ nondegenerateInclusion A).obj Z).isModule =
      ((ambientFunctor e).obj Z).isModule := rfl

/-- Equality of complete maps under inclusion. -/
theorem inclusion_map (hA : IsIdempotented A) (e : Idempotent A)
    {Z Z' : ModuleCat.{uZ} (Idempotent.Corner e)} (f : Z ⟶ Z') :
    (nondegenerateFunctor hA e ⋙ nondegenerateInclusion A).map f =
      (ambientFunctor e).map f := rfl

end Langlands.Algebra.NonUnitalModuleCornerInduction
