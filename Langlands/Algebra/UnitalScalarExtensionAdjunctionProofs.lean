import Langlands.Algebra.UnitalScalarExtensionAdjunctionStatements

/-!
# Renard A.V.2: the scalar-extension adjunction

An explicit native adjunction between the published extension functor on the
balanced quotient and native restriction, with unit `x ↦ 1 ⊗ x` and counit
`a ⊗ y ↦ a • y`. Renard (9 July 2026), A.V.2, printed pp.260–261 / PDF266–267.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open Langlands.Algebra.UnitalScalarExtension

namespace Langlands.Algebra.UnitalScalarExtensionAdjunction

universe uB uA uM uZ

variable {B : Type uB} {A : Type uA} [Ring B] [Ring A] (φ : B →+* A)

section Quotient

variable (M : Type uM) [AddCommGroup M] [Module B M]

/-- Pure tensors are additive in the module variable. -/
theorem tmul_add_right (a : A) (m m' : M) :
    tmul φ M a (m + m') = tmul φ M a m + tmul φ M a m' := by
  let _ := rightModule φ
  let _ := NonUnitalModule.ofModule B M
  exact NonUnitalModuleTensor.tmul_add B A M a m m'

/-- Additive maps out of the balanced quotient are determined by pure tensors. -/
theorem addMonoidHom_ext {Z : Type uZ} [AddCommGroup Z] {f g : Tensor φ M →+ Z}
    (h : ∀ a m, f (tmul φ M a m) = g (tmul φ M a m)) : f = g := by
  let _ := rightModule φ
  let _ := NonUnitalModule.ofModule B M
  exact NonUnitalModuleTensor.hom_ext B h

/-- The published additive descent of a biadditive map balanced through `φ`. -/
def liftAddHom {Z : Type uZ} [AddCommGroup Z] (b : A →+ M →+ Z)
    (hb : ∀ (c : B) (a : A) (m : M), b (a * φ c) m = b a (c • m)) :
    Tensor φ M →+ Z := by
  letI := rightModule φ
  letI := NonUnitalModule.ofModule B M
  exact NonUnitalModuleTensor.lift B b hb

@[simp] theorem liftAddHom_tmul {Z : Type uZ} [AddCommGroup Z] (b : A →+ M →+ Z)
    (hb : ∀ (c : B) (a : A) (m : M), b (a * φ c) m = b a (c • m)) (a : A) (m : M) :
    liftAddHom φ M b hb (tmul φ M a m) = b a m := rfl

end Quotient

section Unit

variable (X : ModuleCat.{max uA uM} B)

/-- The unit component `x ↦ 1 ⊗ x`, B-linear by the balancing relation. -/
def unitMap :
    X ⟶ (restriction.{uB, uA, max uA uM} φ).obj ((functor.{uB, uA, uM} φ).obj X) :=
  ModuleCat.ofHom (Y := (restriction.{uB, uA, max uA uM} φ).obj ((functor.{uB, uA, uM} φ).obj X))
    { toFun := fun x => tmul φ X 1 x
      map_add' := fun x x' => tmul_add_right φ X 1 x x'
      map_smul' := fun b x => by
        rw [RingHom.id_apply, ← tmul_balanced, one_mul]
        exact (congrArg (fun a => tmul φ X a x) (mul_one (φ b))).symm }

theorem unitMap_apply (x : X) : (unitMap φ X).hom x = tmul φ X 1 x := rfl

end Unit

section Counit

variable (Y : ModuleCat.{max uA uM} A)

/-- The action pairing `a, y ↦ a • y`, on the restricted module in its second variable. -/
def actionBiadditive : A →+ (restriction.{uB, uA, max uA uM} φ).obj Y →+ Y :=
  smulAddHom A Y

/-- The action pairing is balanced, since `b` acts on the restriction through `φ b`. -/
theorem actionBiadditive_balanced (c : B) (a : A) (y : (restriction.{uB, uA, max uA uM} φ).obj Y) :
    actionBiadditive φ Y (a * φ c) y = actionBiadditive φ Y a (c • y) :=
  mul_smul a (φ c) (show Y from y)

/-- The additive counit, descended from the balanced action pairing. -/
def counitAddHom : Tensor φ ((restriction.{uB, uA, max uA uM} φ).obj Y) →+ Y :=
  liftAddHom φ ((restriction.{uB, uA, max uA uM} φ).obj Y) (actionBiadditive φ Y)
    (actionBiadditive_balanced φ Y)

theorem counitAddHom_tmul (a : A) (y : (restriction.{uB, uA, max uA uM} φ).obj Y) :
    counitAddHom φ Y (tmul φ _ a y) = a • (show Y from y) := rfl

/-- The descended counit is A-linear for the residual action. -/
theorem counitAddHom_smul (a : A)
    (t : (functor.{uB, uA, uM} φ).obj ((restriction.{uB, uA, max uA uM} φ).obj Y)) :
    counitAddHom φ Y (a • t) = a • counitAddHom φ Y t := by
  have h := addMonoidHom_ext φ ((restriction.{uB, uA, max uA uM} φ).obj Y)
    (f := (counitAddHom φ Y).comp
      (show Tensor φ ((restriction.{uB, uA, max uA uM} φ).obj Y) →+
          Tensor φ ((restriction.{uB, uA, max uA uM} φ).obj Y) from
        NonUnitalModule.toEndHom (residualModule φ _) a))
    (g := (smulAddHom A Y a).comp (counitAddHom φ Y))
    (fun a' y => mul_smul a a' (show Y from y))
  exact DFunLike.congr_fun h t

/-- The counit component `a ⊗ y ↦ a • y`. -/
def counitMap :
    (functor.{uB, uA, uM} φ).obj ((restriction.{uB, uA, max uA uM} φ).obj Y) ⟶ Y :=
  ModuleCat.ofHom (X := (functor.{uB, uA, uM} φ).obj ((restriction.{uB, uA, max uA uM} φ).obj Y))
    { toFun := fun t => counitAddHom φ Y t
      map_add' := map_add (counitAddHom φ Y)
      map_smul' := counitAddHom_smul φ Y }

theorem counitMap_tmul (a : A) (y : (restriction.{uB, uA, max uA uM} φ).obj Y) :
    (counitMap φ Y).hom (tmul φ _ a y) = a • (show Y from y) := rfl

end Counit

/-- The explicit native adjunction, from the unit and counit and both triangle laws. -/
def adjunction : functor.{uB, uA, uM} φ ⊣ restriction.{uB, uA, max uA uM} φ where
  unit :=
    { app := unitMap φ
      naturality := fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl) }
  counit :=
    { app := counitMap φ
      naturality := fun _ _ v => ModuleCat.hom_ext
        (UnitalScalarExtension.hom_ext φ _ fun a y => (v.hom.map_smul a (show _ from y)).symm) }
  left_triangle_components X := ModuleCat.hom_ext
    (UnitalScalarExtension.hom_ext φ X fun a x =>
      congrArg (fun a' => tmul φ X a' x) (mul_one a))
  right_triangle_components Y := ModuleCat.hom_ext
    (LinearMap.ext fun y => one_smul A (show Y from y))

/-- The chosen native adjunction satisfies every published property. -/
theorem adjunction_properties : AdjunctionProperties φ (adjunction φ) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro X Y f x
    rfl
  · intro X Y g a x
    rfl
  · intro X Y f
    exact ((adjunction φ).homEquiv X Y).symm_apply_apply f
  · intro X Y g
    exact ((adjunction φ).homEquiv X Y).apply_symm_apply g
  · intro X' X Y Y' u v f
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  · intro X' X Y Y' u v g
    rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  · intro X x
    rfl
  · intro Y a y
    rfl
  · intro X X' u
    exact (adjunction φ).unit.naturality u
  · intro Y Y' v
    exact (adjunction φ).counit.naturality v
  · exact (adjunction φ).left_triangle_components
  · exact (adjunction φ).right_triangle_components
  · intro X Y f
    rfl
  · intro X Y g
    rfl

/-- The closed scalar-extension adjunction aggregate of Renard A.V.2. -/
theorem scalarExtensionAdjunctionStatements :
    ScalarExtensionAdjunctionStatements.{uB, uA, uM} :=
  fun _ _ _ _ φ => ⟨adjunction φ, adjunction_properties φ⟩

end Langlands.Algebra.UnitalScalarExtensionAdjunction
