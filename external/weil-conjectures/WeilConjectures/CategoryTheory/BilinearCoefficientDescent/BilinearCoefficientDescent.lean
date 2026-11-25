/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import Mathlib.CategoryTheory.Functor.Currying
public import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Bilinear comparisons under coefficient descent

Source: main-20261015, `def-weil-rationalization-karoubi` (raw Hom tensor formula)
and `def-weil-algebraically-closed-coefficients` (common-stage Hom formula).
(blueprint: lem-pur-bilinear-comparison-coefficient-descent).

The algebraic and common-stage assertions are parametrized separately: the latter applies
both before and after the former, and does not assume additive objects or triangulations.
Scalar-first tensors use the recorded ScalarLocalization convention.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] CategoryTheory.Prod.sectL CategoryTheory.Prod.sectR
  CategoryTheory.ScalarLocalization.extension
attribute [local instance 2000] DivisionSemiring.to_moduleIsTorsionFree

set_option linter.unusedSectionVars false

universe r u v u' v' u₂ v₂ u₃ v₃ w

open CategoryTheory TensorProduct

namespace CategoryTheory.BilinearCoefficientDescent

variable {R : Type r} [CommRing R]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]

/-- Separate linearity includes additivity in each variable. Source: raw Hom tensor formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
structure IsSeparatelyLinear (R : Type r) [CommRing R]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]
    (U : C × C ⥤ D) : Prop where
  right :
    ∀ X : C, (Prod.sectR X C ⋙ U).Additive ∧ (Prod.sectR X C ⋙ U).Linear R
  left :
    ∀ Y : C, (Prod.sectL C Y ⋙ U).Additive ∧ (Prod.sectL C Y ⋙ U).Linear R

/-- The exact object and pure-tensor prescriptions for an extension. Source: raw Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
structure IsRawExtension (p : R) (U : C × C ⥤ D)
    (F : ScalarLocalization R C p × ScalarLocalization R C p ⥤
      ScalarLocalization R D p) : Prop where
  linear :
    IsSeparatelyLinear (Localization.Away p) F
  formula :
      (∀ X : ScalarLocalization R C p × ScalarLocalization R C p,
      F.obj X = ⟨U.obj (X.1.obj, X.2.obj)⟩) ∧
    ∀ (X X' Y Y' : C) (f : X ⟶ X') (g : Y ⟶ Y') (a b : Localization.Away p),
      HEq (F.map (X := (⟨X⟩, ⟨Y⟩)) (Y := (⟨X'⟩, ⟨Y'⟩))
        (a ⊗ₜ[R] f, b ⊗ₜ[R] g)) ((a * b) ⊗ₜ[R] U.map (X := (X, Y)) (Y := (X', Y')) (f, g))

@[no_expose] private def tensorComp (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (g : Localization.Away p ⊗[R] (L ⟶ M)) (f : Localization.Away p ⊗[R] (K ⟶ L)) :
    Localization.Away p ⊗[R] (K ⟶ M) :=
  ((ScalarLocalization.composition R C p K L M).toFun g).toFun f

attribute [local implicit_reducible] tensorComp

private theorem tensorComp_zero_left (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (f : Localization.Away p ⊗[R] (K ⟶ L)) :
    tensorComp R C p K L M 0 f = 0 := by
  exact congrArg (fun k ↦ k f) (ScalarLocalization.composition R C p K L M).map_zero

private theorem tensorComp_zero_right (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (g : Localization.Away p ⊗[R] (L ⟶ M)) :
    tensorComp R C p K L M g 0 = 0 := by
  exact ((ScalarLocalization.composition R C p K L M) g).map_zero

private theorem tensorComp_add_left (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (g g' : Localization.Away p ⊗[R] (L ⟶ M))
    (f : Localization.Away p ⊗[R] (K ⟶ L)) :
    tensorComp R C p K L M (g + g') f =
      tensorComp R C p K L M g f + tensorComp R C p K L M g' f := by
  exact congrArg (fun k ↦ k f) ((ScalarLocalization.composition R C p K L M).map_add g g')

private theorem tensorComp_add_right (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (g : Localization.Away p ⊗[R] (L ⟶ M))
    (f f' : Localization.Away p ⊗[R] (K ⟶ L)) :
    tensorComp R C p K L M g (f + f') =
      tensorComp R C p K L M g f + tensorComp R C p K L M g f' := by
  exact ((ScalarLocalization.composition R C p K L M) g).map_add f f'

private theorem tensorComp_tmul (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (f : L ⟶ M) (g : K ⟶ L) (a b : Localization.Away p) :
    tensorComp R C p K L M (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = (a * b) ⊗ₜ[R] (g ≫ f) := by
  exact ScalarLocalization.composition_tmul R C p K L M f g a b

attribute [local simp] tensorComp_zero_left tensorComp_zero_right
  tensorComp_add_left tensorComp_add_right

private theorem hom_add_heq {E : Type u₃} [Category.{v₃} E] [Preadditive E]
    {X Y X' Y' : E} (hx : X = X') (hy : Y = Y')
    {f g : X ⟶ Y} {f' g' : X' ⟶ Y'} (hf : HEq f f') (hg : HEq g g') :
    HEq (f + g) (f' + g') := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg₂ (· + ·) (eq_of_heq hf) (eq_of_heq hg))

@[no_expose] private def integralHom (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U)
    (X X' Y Y' : C) : (X ⟶ X') →ₗ[R] (Y ⟶ Y') →ₗ[R]
      (U.obj (X, Y) ⟶ U.obj (X', Y')) := by
  letI := (hU.1 X').1
  letI := (hU.1 X').2
  letI := (hU.2 Y).1
  letI := (hU.2 Y).2
  exact LinearMap.mk₂ R
    (fun f g ↦ ((Prod.sectL C Y ⋙ U).map f) ≫ ((Prod.sectR X' C ⋙ U).map g))
    (by intros; rw [(Prod.sectL C Y ⋙ U).map_add, Preadditive.add_comp])
    (by intros; rw [(Prod.sectL C Y ⋙ U).map_smul, Linear.smul_comp])
    (by intros; rw [(Prod.sectR X' C ⋙ U).map_add, Preadditive.comp_add])
    (by intros; rw [(Prod.sectR X' C ⋙ U).map_smul, Linear.comp_smul])

private theorem integralHom_apply (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U)
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    integralHom U hU X X' Y Y' f g =
      U.map (X := (X, Y)) (Y := (X', Y')) (f, g) := by
  change U.map (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y) ≫
    U.map (X := (X', Y)) (Y := (X', Y')) (𝟙 X', g) =
      U.map (X := (X, Y)) (Y := (X', Y')) (f, g)
  rw [← U.map_comp]
  congr 1
  exact Prod.ext (Category.comp_id f) (Category.id_comp g)

attribute [local irreducible] integralHom

@[no_expose] private noncomputable def rawHomLinear (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C) :
    (Localization.Away p ⊗[R] (X ⟶ X')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (Y ⟶ Y')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (U.obj (X, Y) ⟶ U.obj (X', Y'))) :=
  TensorProduct.curry
    (((TensorProduct.lift (integralHom U hU X X' Y Y')).baseChange
      (Localization.Away p)).comp
        (AlgebraTensorModule.distribBaseChange R (Localization.Away p)
          (X ⟶ X') (Y ⟶ Y')).symm.toLinearMap)

@[no_expose] private def rawHom (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    Localization.Away p ⊗[R] (U.obj (X, Y) ⟶ U.obj (X', Y')) :=
  ((rawHomLinear p U hU X X' Y Y').toFun f).toFun g

private theorem rawHom_tmul (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) {X X' Y Y' : C}
    (a b : Localization.Away p) (f : X ⟶ X') (g : Y ⟶ Y') :
    rawHom p U hU X X' Y Y' (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) =
      (a * b) ⊗ₜ[R] U.map (f, g) := by
  change rawHomLinear p U hU X X' Y Y' (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = _
  simp only [rawHomLinear, TensorProduct.curry_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgebraTensorModule.distribBaseChange_symm_tmul, LinearMap.baseChange_tmul,
    TensorProduct.lift.tmul, integralHom_apply]

private theorem rawHom_zero_left (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    rawHom p U hU X X' Y Y' 0 g = 0 := by
  exact congrArg (fun k ↦ k g) (rawHomLinear p U hU X X' Y Y').map_zero

private theorem rawHom_zero_right (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (f : Localization.Away p ⊗[R] (X ⟶ X')) :
    rawHom p U hU X X' Y Y' f 0 = 0 := by
  exact ((rawHomLinear p U hU X X' Y Y') f).map_zero

private theorem rawHom_add_left (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (f f' : Localization.Away p ⊗[R] (X ⟶ X')) (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    rawHom p U hU X X' Y Y' (f + f') g =
      rawHom p U hU X X' Y Y' f g + rawHom p U hU X X' Y Y' f' g := by
  exact congrArg (fun k ↦ k g) ((rawHomLinear p U hU X X' Y Y').map_add f f')

private theorem rawHom_add_right (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (f : Localization.Away p ⊗[R] (X ⟶ X')) (g g' : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    rawHom p U hU X X' Y Y' f (g + g') =
      rawHom p U hU X X' Y Y' f g + rawHom p U hU X X' Y Y' f g' := by
  exact ((rawHomLinear p U hU X X' Y Y') f).map_add g g'

private theorem rawHom_smul_left (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (a : Localization.Away p)
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    rawHom p U hU X X' Y Y' (a • f) g = a • rawHom p U hU X X' Y Y' f g := by
  exact congrArg (fun k ↦ k g) ((rawHomLinear p U hU X X' Y Y').map_smul a f)

private theorem rawHom_smul_right (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (a : Localization.Away p)
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    rawHom p U hU X X' Y Y' f (a • g) = a • rawHom p U hU X X' Y Y' f g := by
  exact ((rawHomLinear p U hU X X' Y Y') f).map_smul a g

attribute [local simp] rawHom_zero_left rawHom_zero_right rawHom_add_left rawHom_add_right

attribute [local irreducible] rawHom rawHomLinear ScalarLocalization.composition
  ScalarLocalization.extensionHom ScalarLocalization.coefficientMap

private theorem rawHom_comp (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' X'' Y Y' Y'' : C)
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (f' : Localization.Away p ⊗[R] (X' ⟶ X''))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y'))
    (g' : Localization.Away p ⊗[R] (Y' ⟶ Y'')) :
    rawHom p U hU X X'' Y Y''
        (tensorComp R C p X X' X'' f' f)
        (tensorComp R C p Y Y' Y'' g' g) =
      tensorComp R D p _ _ _
        (rawHom p U hU X' X'' Y' Y'' f' g') (rawHom p U hU X X' Y Y' f g) := by
  induction f using TensorProduct.inductionOn with
  | add f f₁ hf hf₁ => simp only [tensorComp_add_right, rawHom_add_left,
    hf, hf₁]
  | tmul a f =>
    induction f' using TensorProduct.inductionOn with
    | add f' f₁ hf hf₁ => simp only [tensorComp_add_left, rawHom_add_left,
      hf, hf₁]
    | tmul a' f' =>
      induction g using TensorProduct.inductionOn with
      | add g g₁ hg hg₁ => simp only [tensorComp_add_right, rawHom_add_right,
        hg, hg₁]
      | tmul b g =>
        induction g' using TensorProduct.inductionOn with
        | add g' g₁ hg hg₁ => simp only [tensorComp_add_left,
          rawHom_add_right,
          hg, hg₁]
        | tmul b' g' =>
          simp only [tensorComp_tmul, rawHom_tmul]
          rw [← U.map_comp]
          congr 1
          ac_rfl

@[no_expose] private noncomputable def rawFunctor (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) :
    ScalarLocalization R C p × ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj X := ⟨U.obj (X.1.obj, X.2.obj)⟩
  map {X Y} f := rawHom p U hU _ _ _ _ f.1 f.2
  map_id X := by
    change rawHom p U hU _ _ _ _ (1 ⊗ₜ[R] 𝟙 _) (1 ⊗ₜ[R] 𝟙 _) = _
    rw [rawHom_tmul, one_mul]
    exact congrArg (fun f ↦ (1 : Localization.Away p) ⊗ₜ[R] f) (U.map_id _)
  map_comp {X Y Z} f g := rawHom_comp p U hU _ _ _ _ _ _ f.1 g.1 f.2 g.2

attribute [local implicit_reducible] rawFunctor

private theorem rawFunctor_linear (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) : IsSeparatelyLinear (Localization.Away p)
      (rawFunctor p U hU) := by
  constructor
  · intro X
    constructor
    · constructor
      intro Y Y' f g
      exact rawHom_add_right p U hU _ _ _ _ (𝟙 X) f g
    · constructor
      intro Y Y' f a
      exact rawHom_smul_right p U hU _ _ _ _ a (𝟙 X) f
  · intro Y
    constructor
    · constructor
      intro X X' f g
      exact rawHom_add_left p U hU _ _ _ _ f g (𝟙 Y)
    · constructor
      intro X X' f a
      exact rawHom_smul_left p U hU _ _ _ _ a f (𝟙 Y)

/-- Unique raw bilinear extension, including torsion Hom modules.
Source: raw Hom tensor formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, steps 1--2: factor U(f,g) as U(f,1) followed by U(1,g). Separate linearity and
bilinear composition make this bilinear on the two Hom modules. Apply module base change
(def-weil-module-base-change). On pure tensors identity and composition are the integral
functor laws times the product of scalars. Tensor induction gives the laws and uniqueness;
no injectivity into the tensor product is used. -/
theorem raw_extension_existsUnique (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) :
    ∃! F : ScalarLocalization R C p × ScalarLocalization R C p ⥤
      ScalarLocalization R D p, IsRawExtension p U F := by
  refine ⟨rawFunctor p U hU, ⟨rawFunctor_linear p U hU, fun _ ↦ rfl, ?_⟩, ?_⟩
  · intro X X' Y Y' f g a b
    exact heq_of_eq (rawHom_tmul p U hU a b f g)
  · intro F hF
    apply Functor.hext hF.2.1
    rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ f
    let X := (X₁, X₂)
    let Y := (Y₁, Y₂)
    have hh (f₁ : X.1 ⟶ Y.1) (f₂ : X.2 ⟶ Y.2) :
        HEq (integralHom F hF.1 X.1 Y.1 X.2 Y.2 f₁ f₂)
          (rawHom p U hU _ _ _ _ f₁ f₂) := by
      induction f₁ using TensorProduct.inductionOn with
      | tmul a f₁ =>
        induction f₂ using TensorProduct.inductionOn with
        | tmul b f₂ =>
          rw [integralHom_apply, rawHom_tmul]
          exact hF.2.2 _ _ _ _ f₁ f₂ a b
        | add g h hg hh =>
          rw [LinearMap.map_add, rawHom_add_right]
          exact hom_add_heq (hF.2.1 X) (hF.2.1 Y) hg hh
      | add g h hg hh =>
        simp only [rawHom_add_left, LinearMap.map_add,
          LinearMap.add_apply]
        exact hom_add_heq (hF.2.1 X) (hF.2.1 Y) hg hh
    rcases f with ⟨f, g⟩
    simpa only [integralHom_apply, X, Y, rawFunctor] using hh f g

/-- Give a functor its prescribed object function, transporting its morphisms.
Source: transport along object equalities
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def withObjects
    {C₀ : Type u₃} [Category.{v₃} C₀] {D₀ : Type u₂} [Category.{v₂} D₀]
    (F : C₀ ⥤ D₀) (obj : C₀ → D₀) (h : ∀ X, F.obj X = obj X) : C₀ ⥤ D₀ where
  obj := obj
  map {X Y} f := eqToHom (h X).symm ≫ F.map f ≫ eqToHom (h Y)
  map_id X := by
    simp only [F.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
  map_comp f g := by
    simp only [F.map_comp, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]

/-- Object normalization preserves the functor itself.
Source: equality of functors by object equality and heterogeneous map equality
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem withObjects_eq
    {C₀ : Type u₃} [Category.{v₃} C₀] {D₀ : Type u₂} [Category.{v₂} D₀]
    (F : C₀ ⥤ D₀) (obj : C₀ → D₀) (h : ∀ X, F.obj X = obj X) :
    withObjects F obj h = F := by
  unfold withObjects
  apply Functor.hext (fun X ↦ (h X).symm)
  intro X Y f
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- The unique raw extension; all its data are determined by the preceding prescription.
Source: raw Hom tensor formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def raw (p : R) (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U) :=
  withObjects (raw_extension_existsUnique p U hU).exists.choose
    (fun X ↦ ⟨U.obj (X.1.obj, X.2.obj)⟩)
    (raw_extension_existsUnique p U hU).exists.choose_spec.2.1

/-- The raw extension retains the stipulated object.
Source: the uniquely prescribed construction
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem raw_obj (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X : ScalarLocalization R C p × ScalarLocalization R C p) :
    (raw p U hU).obj X = ⟨U.obj (X.1.obj, X.2.obj)⟩ := by
  exact Eq.trans rfl rfl

private theorem id_heq {E : Type*} [Category E] {X Y : E} (h : X = Y) :
    HEq (𝟙 X) (𝟙 Y) := by
  subst Y
  rfl

attribute [local irreducible] raw

omit [Linear R D] in
private theorem extendedHom_tmul {S' : Type u₃} [CommRing S'] [Linear S' D]
    (p : R) (q : S') (φ : R →+* S')
    (h : IsUnit (algebraMap S' (Localization.Away q) (φ p)))
    (F : C ⥤ D) [F.Additive] (hF : ScalarLocalization.IsSemilinear φ F)
    (X Y : C) (a : Localization.Away p) (f : X ⟶ Y) :
    ScalarLocalization.extensionHom p q φ h F hF X Y (a ⊗ₜ[R] f) =
      ScalarLocalization.coefficientMap p q φ h a ⊗ₜ[S'] F.map f :=
  by
    unfold ScalarLocalization.extensionHom
    exact (ScalarLocalization.existsUnique_semilinearHom p q φ h F hF X Y).exists.choose_spec a f

section RawWhiskering

variable {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear R E]

private theorem coefficientMap_id (p : R) :
    ScalarLocalization.coefficientMap p p (RingHom.id R)
      (IsLocalization.Away.algebraMap_isUnit p) = RingHom.id (Localization.Away p) := by
  symm
  apply (ScalarLocalization.coefficientMap_unique _ _ _ _ _).1
  rfl

omit [Preadditive D] in
private theorem map_heq {D₀ : Type u₃} [Category.{v₃} D₀]
    (F : D ⥤ D₀) {X Y X' Y' : D} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

end RawWhiskering

attribute [local implicit_reducible] StageSystem.Morphism.functor StageSystem.ι


section CommonStage

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {A : I → Type u} [∀ i, Category.{v} (A i)]
  {A₂ : I → Type u₂} [∀ i, Category.{v₂} (A₂ i)]
  {B : I → Type u'} [∀ i, Category.{v'} (B i)]
  (S : StageSystem A) (S₂ : StageSystem A₂) (T : StageSystem B)

/-- The family of identity comparisons, with its unchanged component type.
Source: supplied common-stage units
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def UnitComparisons (S : StageSystem A) := ∀ i, S.T (le_refl i) ≅ 𝟭 (A i)

/-- The two cocycles stored with specified identity comparisons.
Source: common-stage unit equations
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def UnitLaws (S : StageSystem A) (unit : ∀ i, S.T (le_refl i) ≅ 𝟭 (A i)) :
    Prop :=
  (∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((unit i).hom.app X)) ∧
    (∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc h (le_refl j)).hom.app X = (unit j).hom.app ((S.T h).obj X))

/-- Specified identity comparisons and their two unit cocycles.
Source: common-stage formula, supplied identity and tower isomorphisms
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def Units (S : StageSystem A) :=
  {unit : UnitComparisons S // UnitLaws S unit}

namespace Units

@[no_expose, implicit_reducible] def unit {S : StageSystem A} (uS : Units S) :
    ∀ i, S.T (le_refl i) ≅ 𝟭 (A i) := uS.val

omit [IsDirectedOrder I] in
theorem left {S : StageSystem A} (uS : Units S) {i j : I} (h : i ≤ j) (X : A i) :
    (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((uS.unit i).hom.app X) :=
  uS.property.1 h X

omit [IsDirectedOrder I] in
theorem right {S : StageSystem A} (uS : Units S) {i j : I} (h : i ≤ j) (X : A i) :
    (S.assoc h (le_refl j)).hom.app X = (uS.unit j).hom.app ((S.T h).obj X) :=
  uS.property.2 h X

@[no_expose] def mk {S : StageSystem A} (unit : ∀ i, S.T (le_refl i) ≅ 𝟭 (A i))
    (left : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((unit i).hom.app X))
    (right : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc h (le_refl j)).hom.app X = (unit j).hom.app ((S.T h).obj X)) :
    Units S := ⟨unit, left, right⟩

end Units

/-- The tower law stored in a bilinear family.
Source: common-stage comparison cocycle
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def FamilyTower (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j) : Prop :=
  ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y)

/-- A bilinear family with the specified scalar comparison and its tower equation.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Linearity is imposed separately at integral stages, not on this purely categorical interface. -/
structure Family where
  mkData ::
  functors : ∀ i, A i × A₂ i ⥤ B i
  comparisons : ∀ {i j : I} (h : i ≤ j),
    functors i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ functors j
  coherence : FamilyTower S S₂ T functors comparisons

namespace Family

variable {S S₂ T}

@[no_expose, implicit_reducible] def U (F : Family S S₂ T) : ∀ i, A i × A₂ i ⥤ B i := F.functors

@[no_expose, implicit_reducible] def comparison (F : Family S S₂ T) {i j : I} (h : i ≤ j) :
    F.U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ F.U j := F.comparisons h

omit [IsDirectedOrder I] in
theorem tower (F : Family S S₂ T) :
    ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((F.comparison h).hom.app (X, Y)) ≫
      (F.comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (F.U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((F.U i).obj (X, Y)) ≫
      (F.comparison (h.trans h')).hom.app (X, Y) :=
  F.coherence

@[no_expose] def mk (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j)
    (tower : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y)) : Family S S₂ T := Family.mkData U comparison tower

end Family

variable {S S₂ T}

/-- The identity cocycle for the supplied bilinear scalar comparison.
Source: common-stage formula, supplied λ identity cocycle
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
def HasUnitComparison (U : Family S S₂ T) (uS : Units S) (uS₂ : Units S₂)
    (uT : Units T) : Prop :=
  ∀ (i : I) (X : A i) (Y : A₂ i),
    (U.comparison (le_refl i)).hom.app (X, Y) ≫
      (U.U i).map (X := ((S.T (le_refl i)).obj X, (S₂.T (le_refl i)).obj Y))
        (Y := (X, Y)) ((uS.unit i).hom.app X, (uS₂.unit i).hom.app Y) =
        (uT.unit i).hom.app ((U.U i).obj (X, Y))

/-- The scalar square stored in a compatible transformation.
Source: common-stage transformation formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def TransformationSquare (U V : Family S S₂ T)
    (app : ∀ i, U.U i ⟶ V.U i) : Prop :=
  ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
    (T.T h).map ((app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
      (U.comparison h).hom.app (X, Y) ≫
        (app j).app ((S.T h).obj X, (S₂.T h).obj Y)

/-- Compatible transformations, including the scalar square of the statement.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
structure Transformation (U V : Family S S₂ T) where
  mkData ::
  components : ∀ i, U.U i ⟶ V.U i
  compatibility : TransformationSquare U V components

namespace Transformation

variable {U V : Family S S₂ T}

@[no_expose, implicit_reducible] def app (η : Transformation U V) (i : I) :
    U.U i ⟶ V.U i := η.components i

omit [IsDirectedOrder I] in
theorem square (η : Transformation U V) :
    ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
    (T.T h).map ((η.app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
      (U.comparison h).hom.app (X, Y) ≫
        (η.app j).app ((S.T h).obj X, (S₂.T h).obj Y) := η.compatibility

@[no_expose] def mk (app : ∀ i, U.U i ⟶ V.U i)
    (square : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
      (T.T h).map ((app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
        (U.comparison h).hom.app (X, Y) ≫
          (app j).app ((S.T h).obj X, (S₂.T h).obj Y)) : Transformation U V :=
  Transformation.mkData app square

end Transformation

/-- The specified common-field output object. Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
def output (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) : T.PairCategory :=
  ⟨join X.1.stage X.2.stage,
    (U.U _).obj (X.1.toStage (left _ _), X.2.toStage (right _ _))⟩

/-- The endpoint identification d from the node's proof, using both input associators.
Source: common-stage Hom formula, proof step 7
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
def endpoint (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) {L : I}
    (h : join X.1.stage X.2.stage ≤ L) :
    (T.T h).obj (output U join left right X).obj ≅
      (U.U L).obj (X.1.toStage ((left _ _).trans h),
        X.2.toStage ((right _ _).trans h)) :=
  (U.comparison h).app _ ≪≫ (U.U L).mapIso
    (Iso.prod ((S.assoc (left _ _) h).app X.1.obj)
      ((S₂.assoc (right _ _) h).app X.2.obj))

/-- The explicit object and common-stage arrow formulas, with equality of transported endpoints.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
structure IsDescent (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (F : S.PairCategory × S₂.PairCategory ⥤ T.PairCategory) : Prop where
  objects :
    ∀ X, F.obj X = output U join left right X
  arrows :
    ∀ (X Y : S.PairCategory × S₂.PairCategory) (L : I)
      (hX : join X.1.stage X.2.stage ≤ L) (hY : join Y.1.stage Y.2.stage ≤ L)
      (f : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
      (g : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)),
      HEq (F.map (StageSystem.PairCategory.mkHom L _ _ f,
        StageSystem.PairCategory.mkHom L _ _ g))
        (StageSystem.PairCategory.mkHom (X := output U join left right X)
          (Y := output U join left right Y) L hX hY
          ((endpoint U join left right X hX).hom ≫ (U.U L).map (f, g) ≫
            (endpoint U join left right Y hY).inv))

/-- The specification record is equivalent to its original two clauses.
Source: the unchanged specification in this module
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem isDescent_iff (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (F : S.PairCategory × S₂.PairCategory ⥤ T.PairCategory) :
    IsDescent U join left right F ↔
  (∀ X, F.obj X = output U join left right X) ∧
  ∀ (X Y : S.PairCategory × S₂.PairCategory) (L : I)
    (hX : join X.1.stage X.2.stage ≤ L) (hY : join Y.1.stage Y.2.stage ≤ L)
    (f : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
    (g : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)),
    HEq (F.map (StageSystem.PairCategory.mkHom L _ _ f,
      StageSystem.PairCategory.mkHom L _ _ g))
      (StageSystem.PairCategory.mkHom (X := output U join left right X)
        (Y := output U join left right Y) L hX hY
        ((endpoint U join left right X hX).hom ≫ (U.U L).map (f, g) ≫
          (endpoint U join left right Y hY).inv)) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩

@[no_expose] private def productSystem (S : StageSystem A) (S₂ : StageSystem A₂) :
    StageSystem (fun i ↦ A i × A₂ i) where
  T h := (S.T h).prod (S₂.T h)
  assoc h h' := NatIso.ofComponents
    (fun X ↦ Iso.prod ((S.assoc h h').app X.1) ((S₂.assoc h h').app X.2))
    (by
      intro X Y f
      exact Prod.ext ((S.assoc h h').hom.naturality f.1)
        ((S₂.assoc h h').hom.naturality f.2))
  cocycle h h' h'' X := Prod.ext (S.cocycle h h' h'' X.1) (S₂.cocycle h h' h'' X.2)

@[no_expose] private def familyMorphism (U : Family S S₂ T) : (productSystem S S₂).Morphism T where
  Φ := U.U
  β := U.comparison
  coh h h' X := U.tower h h' X.1 X.2

@[no_expose] private def projectionLeft (S : StageSystem A) (S₂ : StageSystem A₂) :
    (productSystem S S₂).Morphism S where
  Φ i := Prod.fst (A i) (A₂ i)
  β _ := Iso.refl _
  coh h h' X := by
    change (S.T h').map (𝟙 _) ≫ 𝟙 _ ≫ (S.assoc h h').hom.app X.1 =
      (S.assoc h h').hom.app X.1 ≫ 𝟙 _
    simp

@[no_expose] private def projectionRight (S : StageSystem A) (S₂ : StageSystem A₂) :
    (productSystem S S₂).Morphism S₂ where
  Φ i := Prod.snd (A i) (A₂ i)
  β _ := Iso.refl _
  coh h h' X := by
    change (S₂.T h').map (𝟙 _) ≫ 𝟙 _ ≫ (S₂.assoc h h').hom.app X.2 =
      (S₂.assoc h h').hom.app X.2 ≫ 𝟙 _
    simp

@[no_expose] private def diagonal (S : StageSystem A) (S₂ : StageSystem A₂) :
    (productSystem S S₂).PairCategory ⥤ S.PairCategory × S₂.PairCategory where
  obj X := (⟨X.stage, X.obj.1⟩, ⟨X.stage, X.obj.2⟩)
  map f := ((projectionLeft S S₂).functor.prod' (projectionRight S S₂).functor).map f
  map_id X := ((projectionLeft S S₂).functor.prod'
    (projectionRight S S₂).functor).map_id X
  map_comp f g := ((projectionLeft S S₂).functor.prod'
    (projectionRight S S₂).functor).map_comp f g

attribute [local implicit_reducible] productSystem familyMorphism projectionLeft
  projectionRight diagonal

private theorem diagonal_map (S : StageSystem A) (S₂ : StageSystem A₂)
    {X Y : (productSystem S S₂).PairCategory} {n : I}
    (hX : X.stage ≤ n) (hY : Y.stage ≤ n) (f : X.toStage hX ⟶ Y.toStage hY) :
    (diagonal S S₂).map (StageSystem.PairCategory.mkHom n hX hY f) =
      (StageSystem.PairCategory.mkHom
        (X := ⟨X.stage, X.obj.1⟩) (Y := ⟨Y.stage, Y.obj.1⟩) n hX hY f.1,
        StageSystem.PairCategory.mkHom
          (X := ⟨X.stage, X.obj.2⟩) (Y := ⟨Y.stage, Y.obj.2⟩) n hX hY f.2) := by
  change (StageSystem.PairCategory.mkHom (S := S)
      (X := ⟨X.stage, X.obj.1⟩) (Y := ⟨Y.stage, Y.obj.1⟩) n hX hY (𝟙 _ ≫ f.1 ≫ 𝟙 _),
    StageSystem.PairCategory.mkHom (S := S₂)
      (X := ⟨X.stage, X.obj.2⟩) (Y := ⟨Y.stage, Y.obj.2⟩) n hX hY (𝟙 _ ≫ f.2 ≫ 𝟙 _)) = _
  simp only [Category.id_comp, Category.comp_id]

private theorem diagonal_bijective (S : StageSystem A) (S₂ : StageSystem A₂)
    (X Y : (productSystem S S₂).PairCategory) :
    Function.Bijective ((diagonal S S₂).map (X := X) (Y := Y)) := by
  constructor
  · intro f g he
    induction f using StageSystem.PairCategory.hom_induction with
    | h n hX hY u =>
      induction g using StageSystem.PairCategory.hom_induction with
      | h m hX' hY' v =>
        rw [diagonal_map, diagonal_map] at he
        obtain ⟨p, hn, hm, hp⟩ :=
          (StageSystem.PairCategory.mkHom_eq_mkHom_iff' (S := S)
            (X := ⟨X.stage, X.obj.1⟩) (Y := ⟨Y.stage, Y.obj.1⟩) u.1 v.1).1
              (congrArg _root_.Prod.fst he)
        obtain ⟨q, hn', hm', hq⟩ :=
          (StageSystem.PairCategory.mkHom_eq_mkHom_iff' (S := S₂)
            (X := ⟨X.stage, X.obj.2⟩) (Y := ⟨Y.stage, Y.obj.2⟩) u.2 v.2).1
              (congrArg _root_.Prod.snd he)
        obtain ⟨r, hpr, hqr⟩ := exists_ge_ge p q
        apply (StageSystem.PairCategory.mkHom_eq_mkHom_iff' u v).2
        refine ⟨r, hn.trans hpr, hm.trans hpr, ?_⟩
        apply Prod.ext
        · change S.tr (hn.trans hpr) u.1 = S.tr (hm.trans hpr) v.1
          have hr := congrArg (S.tr hpr) hp
          simpa only [S.tr_tr] using hr
        · change S₂.tr (hn.trans hpr) u.2 = S₂.tr (hm.trans hpr) v.2
          have hr := congrArg (S₂.tr hqr) hq
          simpa only [S₂.tr_tr] using hr
  · rintro ⟨f, g⟩
    obtain ⟨n, hn, hX, hY, u, rfl⟩ := StageSystem.PairCategory.exists_le_mkHom_eq f X.stage
    obtain ⟨m, hm, hX', hY', v, rfl⟩ := StageSystem.PairCategory.exists_le_mkHom_eq g n
    refine ⟨StageSystem.PairCategory.mkHom m (hX.trans hm) (hY.trans hm)
      (S.tr hm u, v), ?_⟩
    rw [diagonal_map, StageSystem.PairCategory.mkHom_tr]

@[no_expose] private def diagonalFF (S : StageSystem A) (S₂ : StageSystem A₂) :
    (diagonal S S₂).FullyFaithful :=
  ((Functor.FullyFaithful.nonempty_iff_map_bijective _).2 (diagonal_bijective S S₂)).some

@[no_expose] private def pairedObject (S : StageSystem A) (S₂ : StageSystem A₂) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) : (productSystem S S₂).PairCategory :=
  ⟨join X.1.stage X.2.stage,
    (X.1.toStage (left _ _), X.2.toStage (right _ _))⟩

@[no_expose] private def pairedIso (S : StageSystem A) (S₂ : StageSystem A₂) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) :
    (diagonal S S₂).obj (pairedObject S S₂ join left right X) ≅ X :=
  Iso.prod (S.isoToStage X.1 (left _ _)).symm
    (S₂.isoToStage X.2 (right _ _)).symm

@[no_expose] private def pairing (S : StageSystem A) (S₂ : StageSystem A₂) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    S.PairCategory × S₂.PairCategory ⥤ (productSystem S S₂).PairCategory where
  obj := pairedObject S S₂ join left right
  map {X Y} f := (diagonalFF S S₂).preimage
    ((pairedIso S S₂ join left right X).hom ≫ f ≫
      (pairedIso S S₂ join left right Y).inv)
  map_id X := by
    apply (diagonalFF S S₂).map_injective
    rw [(diagonalFF S S₂).map_preimage]
    simp
  map_comp {X Y Z} f g := by
    apply (diagonalFF S S₂).map_injective
    rw [Functor.map_comp]
    simp only [(diagonalFF S S₂).map_preimage, Category.assoc, Iso.inv_hom_id_assoc]

attribute [local implicit_reducible] pairedObject pairedIso pairing output endpoint

private theorem isoToStage_hom_eq (X : S.PairCategory) {j k : I}
    (a : X.stage ≤ j) (b : j ≤ k) :
    (S.isoToStage X a).hom = StageSystem.PairCategory.mkHom
      (X := X) (Y := (S.ι j).obj (X.toStage a))
      k (a.trans b) b ((S.assoc a b).inv.app X.obj) := by
  change StageSystem.PairCategory.mkHom j a (le_refl j) _ = _
  rw [← StageSystem.PairCategory.mkHom_tr b]
  apply congrArg (StageSystem.PairCategory.mkHom
    (X := X) (Y := (S.ι j).obj (X.toStage a)) k (a.trans b) b)
  dsimp only [StageSystem.tr]
  rw [← Category.assoc, S.cocycle_inv a (le_refl j) b, Category.assoc,
    Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem isoToStage_inv_eq (X : S.PairCategory) {j k : I}
    (a : X.stage ≤ j) (b : j ≤ k) :
    (S.isoToStage X a).inv = StageSystem.PairCategory.mkHom
      (X := (S.ι j).obj (X.toStage a)) (Y := X)
      k b (a.trans b) ((S.assoc a b).hom.app X.obj) := by
  apply (cancel_epi (S.isoToStage X a).hom).1
  rw [Iso.hom_inv_id, isoToStage_hom_eq X a b,
    StageSystem.PairCategory.mkHom_comp_mkHom,
    StageSystem.PairCategory.id_eq_mkHom X (a.trans b)]
  simp

private theorem conjugate_mkHom {X Y : S.PairCategory} {j j' k : I}
    (a : X.stage ≤ j) (a' : Y.stage ≤ j') (b : j ≤ k) (b' : j' ≤ k)
    (f : X.toStage (a.trans b) ⟶ Y.toStage (a'.trans b')) :
    (S.isoToStage X a).inv ≫ StageSystem.PairCategory.mkHom k _ _ f ≫
      (S.isoToStage Y a').hom =
    StageSystem.PairCategory.mkHom
      (X := (S.ι j).obj (X.toStage a)) (Y := (S.ι j').obj (Y.toStage a')) k b b'
      ((S.assoc a b).hom.app X.obj ≫ f ≫ (S.assoc a' b').inv.app Y.obj) := by
  rw [isoToStage_inv_eq X a b, isoToStage_hom_eq Y a' b',
    StageSystem.PairCategory.mkHom_comp_mkHom, StageSystem.PairCategory.mkHom_comp_mkHom]

private theorem pairing_map (S : StageSystem A) (S₂ : StageSystem A₂) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X Y : S.PairCategory × S₂.PairCategory) (L : I)
    (hX : join X.1.stage X.2.stage ≤ L) (hY : join Y.1.stage Y.2.stage ≤ L)
    (f : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
    (g : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)) :
    (pairing S S₂ join left right).map
      (StageSystem.PairCategory.mkHom L _ _ f, StageSystem.PairCategory.mkHom L _ _ g) =
      StageSystem.PairCategory.mkHom L hX hY
        ((S.assoc (left _ _) hX).hom.app X.1.obj ≫ f ≫
            (S.assoc (left _ _) hY).inv.app Y.1.obj,
          (S₂.assoc (right _ _) hX).hom.app X.2.obj ≫ g ≫
            (S₂.assoc (right _ _) hY).inv.app Y.2.obj) := by
  apply (diagonalFF S S₂).map_injective
  rw [diagonal_map]
  change (diagonal S S₂).map ((diagonalFF S S₂).preimage _) = _
  rw [(diagonalFF S S₂).map_preimage]
  exact Prod.ext (conjugate_mkHom _ _ _ _ f) (conjugate_mkHom _ _ _ _ g)

private theorem exists_joint_representative
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X Y : S.PairCategory × S₂.PairCategory) (f : X.1 ⟶ Y.1) (g : X.2 ⟶ Y.2) :
    ∃ (L : I) (hX : join X.1.stage X.2.stage ≤ L)
      (hY : join Y.1.stage Y.2.stage ≤ L)
      (u : X.1.toStage ((left _ _).trans hX) ⟶ Y.1.toStage ((left _ _).trans hY))
      (v : X.2.toStage ((right _ _).trans hX) ⟶ Y.2.toStage ((right _ _).trans hY)),
      f = StageSystem.PairCategory.mkHom L _ _ u ∧
        g = StageSystem.PairCategory.mkHom L _ _ v := by
  obtain ⟨m, hmX, hmY⟩ := exists_ge_ge (join X.1.stage X.2.stage) (join Y.1.stage Y.2.stage)
  obtain ⟨n, hmn, hX, hY, u, rfl⟩ := StageSystem.PairCategory.exists_le_mkHom_eq f m
  obtain ⟨L, hnL, hX', hY', v, rfl⟩ := StageSystem.PairCategory.exists_le_mkHom_eq g n
  exact ⟨L, hmX.trans (hmn.trans hnL), hmY.trans (hmn.trans hnL),
    S.tr hnL u, v, (StageSystem.PairCategory.mkHom_tr hnL u).symm, rfl⟩

@[no_expose] private def explicitDescent (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    S.PairCategory × S₂.PairCategory ⥤ T.PairCategory where
  obj X := output U join left right X
  map f := (pairing S S₂ join left right ⋙ (familyMorphism U).functor).map f
  map_id X := (pairing S S₂ join left right ⋙ (familyMorphism U).functor).map_id X
  map_comp f g := (pairing S S₂ join left right ⋙ (familyMorphism U).functor).map_comp f g

private theorem explicitDescent_spec (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    IsDescent U join left right (explicitDescent U join left right) := by
  refine ⟨fun _ ↦ rfl, ?_⟩
  intro X Y L hX hY f g
  apply heq_of_eq
  dsimp only [explicitDescent, Functor.comp_map]
  rw [pairing_map S S₂ join left right X Y L hX hY f g,
    StageSystem.Morphism.functor_map_mkHom]
  apply congrArg (StageSystem.PairCategory.mkHom L hX hY)
  dsimp only [StageSystem.Morphism.mapAt, familyMorphism, endpoint, Iso.trans_hom,
    Iso.trans_inv, Iso.app, Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Iso.prod_hom, Iso.prod_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [prod_comp, Category.assoc]
  rfl

/-- Existence and uniqueness of the descended bifunctor with its explicit representatives.
Source: common-stage Hom formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, steps 5--9: choose a common upper stage for two arrow representatives and the output
fields. Conjugate U_L(f,g) by the endpoint identifications. The comparison tower equation,
the two input associator cocycles and comparison naturality show that this commutes with
transport. Equality of representatives is equality after a further common stage, so the
formula factors through the actual quotient Hom. Identity and composition follow by
cancelling adjacent endpoint isomorphisms. Every arrow has a representative, giving uniqueness.
This is the pair-category model of def-weil-algebraically-closed-coefficients, used without
any geometric, additive-object or triangulated hypotheses. -/
theorem descent_existsUnique (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    ∃! F : S.PairCategory × S₂.PairCategory ⥤ T.PairCategory,
      IsDescent U join left right F := by
  refine ⟨explicitDescent U join left right, explicitDescent_spec U join left right, ?_⟩
  intro F hF
  apply Functor.hext hF.1
  rintro X Y ⟨f, g⟩
  obtain ⟨L, hX, hY, u, v, rfl, rfl⟩ :=
    exists_joint_representative join left right X Y f g
  exact (hF.2 X Y L hX hY u v).trans
    ((explicitDescent_spec U join left right).2 X Y L hX hY u v).symm

/-- The unique representative-normalized descended bifunctor.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def descend (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :=
  withObjects (descent_existsUnique U join left right).exists.choose
    (output U join left right)
    (descent_existsUnique U join left right).exists.choose_spec.1

/-- The chosen common-stage functor satisfies the complete representative prescription.
Source: the proved unique descent
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem descend_spec (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    IsDescent U join left right (descend U join left right) := by
  unfold descend
  rw [withObjects_eq]
  exact (descent_existsUnique U join left right).exists.choose_spec

attribute [local implicit_reducible] explicitDescent

private theorem descend_eq (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    descend U join left right = explicitDescent U join left right :=
  (descent_existsUnique U join left right).unique
    (descend_spec U join left right)
    (explicitDescent_spec U join left right)

attribute [local irreducible] descend

@[no_expose] private def pairingComparison (j k : I → I → I)
    (jl : ∀ a b, a ≤ j a b) (jr : ∀ a b, b ≤ j a b)
    (kl : ∀ a b, a ≤ k a b) (kr : ∀ a b, b ≤ k a b) :
    pairing S S₂ j jl jr ≅ pairing S S₂ k kl kr :=
  NatIso.ofComponents
    (fun X ↦ (diagonalFF S S₂).preimageIso
      (pairedIso S S₂ j jl jr X ≪≫ (pairedIso S S₂ k kl kr X).symm)) (by
        intro X Y f
        apply (diagonalFF S S₂).map_injective
        simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
          (diagonalFF S S₂).map_preimage]
        change (diagonal S S₂).map ((diagonalFF S S₂).preimage _) ≫ _ =
          _ ≫ (diagonal S S₂).map ((diagonalFF S S₂).preimage _)
        simp only [(diagonalFF S S₂).map_preimage]
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
          Iso.inv_hom_id_assoc])

@[no_expose] private def descentComparison (U : Family S S₂ T) (j k : I → I → I)
    (jl : ∀ a b, a ≤ j a b) (jr : ∀ a b, b ≤ j a b)
    (kl : ∀ a b, a ≤ k a b) (kr : ∀ a b, b ≤ k a b) :
    descend U j jl jr ≅ descend U k kl kr :=
  eqToIso (descend_eq U j jl jr) ≪≫
    Functor.isoWhiskerRight (pairingComparison j k jl jr kl kr) (familyMorphism U).functor ≪≫
      (eqToIso (descend_eq U k kl kr)).symm

attribute [local irreducible] productSystem projectionLeft projectionRight diagonal diagonalFF
  pairedObject pairedIso pairing

section InputLeft

variable
    {A₀ : I → Type u₃} [∀ i, Category.{v₃} (A₀ i)] {S₀ : StageSystem A₀}
    (F : S₀.Morphism S) (U : Family S S₂ T) (UF : Family S₀ S₂ T)
    (hU : ∀ i, UF.U i = ((F.Φ i).prod (𝟭 (A₂ i))) ⋙ U.U i)
    (cU : ∀ {i j : I} (h : i ≤ j) (X : A₀ i) (Y : A₂ i),
      HEq ((UF.comparison h).hom.app (X, Y))
        ((U.comparison h).hom.app ((F.Φ i).obj X, Y) ≫
          (U.U j).map (X := ((S.T h).obj ((F.Φ i).obj X), (S₂.T h).obj Y))
            (Y := ((F.Φ j).obj ((S₀.T h).obj X), (S₂.T h).obj Y))
            ((F.β h).hom.app X, 𝟙 _)))
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)

end InputLeft

section InputRight

variable
    {A₀ : I → Type u₃} [∀ i, Category.{v₃} (A₀ i)] {S₀ : StageSystem A₀}
    (F : S₀.Morphism S₂) (U : Family S S₂ T) (UF : Family S S₀ T)
    (hU : ∀ i, UF.U i = ((𝟭 (A i)).prod (F.Φ i)) ⋙ U.U i)
    (cU : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₀ i),
      HEq ((UF.comparison h).hom.app (X, Y))
        ((U.comparison h).hom.app (X, (F.Φ i).obj Y) ≫
          (U.U j).map (X := ((S.T h).obj X, (S₂.T h).obj ((F.Φ i).obj Y)))
            (Y := ((S.T h).obj X, (F.Φ j).obj ((S₀.T h).obj Y)))
            (𝟙 _, (F.β h).hom.app Y)))
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)

end InputRight

end CommonStage

section RationalSystems

variable {I : Type w} [Preorder I]
  {O : I → Type r} [∀ i, CommRing (O i)] (π : ∀ i, O i)
  (φ : ∀ {i j : I}, i ≤ j → O i →+* O j)
  (unitImage : ∀ {i j : I} (h : i ≤ j),
    IsUnit (algebraMap (O j) (Localization.Away (π j)) (φ h (π i))))
  {A : I → Type u} [∀ i, Category.{v} (A i)]
  [∀ i, Preadditive (A i)] [∀ i, Linear (O i) (A i)]
  (S : StageSystem A) [∀ (i j : I) (h : i ≤ j), (S.T h).Additive]
  (semi : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (S.T h))

private theorem coefficientMap_comp {i j k : I} (h : i ≤ j) (h' : j ≤ k)
    (φcomp : (φ h').comp (φ h) = φ (h.trans h')) :
    (ScalarLocalization.coefficientMap (π j) (π k) (φ h') (unitImage h')).comp
      (ScalarLocalization.coefficientMap (π i) (π j) (φ h) (unitImage h)) =
      ScalarLocalization.coefficientMap (π i) (π k) (φ (h.trans h'))
        (unitImage (h.trans h')) := by
  apply (ScalarLocalization.coefficientMap_unique _ _ _ _ _).1
  ext r
  simp only [RingHom.comp_apply, ScalarLocalization.coefficientMap,
    IsLocalization.Away.lift_eq]
  exact congrArg (algebraMap (O k) (Localization.Away (π k))) (RingHom.congr_fun φcomp r)

variable {π φ unitImage S semi}

private theorem rationalComparison_naturality
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    (T : StageSystem B) [∀ (i j : I) (h : i ≤ j), (T.T h).Additive]
    (semiT : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (T.T h))
    (U : Family S S T) (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    {i j : I} (h : i ≤ j) (X X' Y Y' : A i)
    (f : Localization.Away (π i) ⊗[O i] (X ⟶ X'))
    (g : Localization.Away (π i) ⊗[O i] (Y ⟶ Y')) :
    tensorComp (O j) (B j) (π j) _ _ _
        (1 ⊗ₜ[O j] (U.comparison h).hom.app (X', Y'))
        (ScalarLocalization.extensionHom (π i) (π j) (φ h) (unitImage h)
          (T.T h) (semiT h) ((U.U i).obj (X, Y)) ((U.U i).obj (X', Y'))
          (rawHom (π i) (U.U i) (hU i) X X' Y Y' f g)) =
      tensorComp (O j) (B j) (π j) _ _ _
        (rawHom (π j) (U.U j) (hU j)
          ((S.T h).obj X) ((S.T h).obj X') ((S.T h).obj Y) ((S.T h).obj Y')
          (ScalarLocalization.extensionHom (π i) (π j) (φ h) (unitImage h)
            (S.T h) (semi h) X X' f)
          (ScalarLocalization.extensionHom (π i) (π j) (φ h) (unitImage h)
            (S.T h) (semi h) Y Y' g))
        (1 ⊗ₜ[O j] (U.comparison h).hom.app (X, Y)) := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' =>
    simp only [tensorComp_add_left, tensorComp_add_right, rawHom_add_left,
      AddMonoidHom.map_add]
    exact congrArg₂ (· + ·) hf hf'
  | tmul a f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' =>
      simp only [tensorComp_add_left, tensorComp_add_right, rawHom_add_right,
        AddMonoidHom.map_add]
      exact congrArg₂ (· + ·) hg hg'
    | tmul b g =>
      rw [rawHom_tmul, extendedHom_tmul, extendedHom_tmul, extendedHom_tmul,
        rawHom_tmul, map_mul, tensorComp_tmul,
        tensorComp_tmul, one_mul, mul_one]
      exact congrArg (fun f ↦
        (ScalarLocalization.coefficientMap (π i) (π j) (φ h) (unitImage h) a *
          ScalarLocalization.coefficientMap (π i) (π j) (φ h) (unitImage h) b) ⊗ₜ[O j] f)
        ((U.comparison h).hom.naturality (X := (X,Y)) (Y := (X',Y')) (f,g))

@[no_expose] private def rationalComparisonIso
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    (T : StageSystem B) [∀ (i j : I) (h : i ≤ j), (T.T h).Additive]
    (semiT : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (T.T h))
    (U : Family S S T) (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    {i j : I} (h : i ≤ j) :
    rawFunctor (π i) (U.U i) (hU i) ⋙
        ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (T.T h) (semiT h) ≅
      (ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h)).prod
        (ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h)) ⋙
        rawFunctor (π j) (U.U j) (hU j) :=
  NatIso.ofComponents
    (fun X ↦ (ScalarLocalization.localization (O j) (B j) (π j)).mapIso
      ((U.comparison h).app (X.1.obj, X.2.obj))) (by
        intro X Y f
        exact rationalComparison_naturality T semiT U hU h
          X.1.obj Y.1.obj X.2.obj Y.2.obj f.1 f.2)

attribute [local irreducible] Units HasUnitComparison

end RationalSystems

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer

section PadicCoefficients

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The recorded valuation rings, indexed by the genuine finite intermediate extensions.
Source: blueprint coefficient definitions
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def Integers (E : Padic.FiniteCoefficientFields l Ω) : Subring E.val :=
  Padic.coefficientExtensionIntegers l E.val

/-- The named integer ring is exactly the recorded coefficient-extension subring.
Source: coefficient ring definition
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem Integers_eq (E : Padic.FiniteCoefficientFields l Ω) :
    Integers l Ω E = Padic.coefficientExtensionIntegers l E.val := by
  exact Eq.trans rfl rfl



/-- The recorded uniformizer belongs to the named integer subring.
Source: the coefficient uniformizer definition and `Integers_eq`
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
theorem uniformizer_mem (E : Padic.FiniteCoefficientFields l Ω) :
    (Padic.coefficientExtensionUniformizer l E.val : E.val) ∈ Integers l Ω E := by
  rw [Integers_eq]
  exact (Padic.coefficientExtensionUniformizer l E.val).property

/-- The recorded uniformizer; no extra torsion-free or characteristic hypotheses.
Source: blueprint coefficient definitions
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def uniformizer (E : Padic.FiniteCoefficientFields l Ω) : Integers l Ω E :=
  ⟨(Padic.coefficientExtensionUniformizer l E.val : E.val), uniformizer_mem l Ω E⟩

set_option linter.unusedSectionVars false in
attribute [local irreducible] Padic.finiteCoefficientCompositum uniformizer

/-- The chosen output field is exactly the compositum, including the base-field case.
Source: common-stage formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent).
Proof, step 5: finiteCoefficientFields_properties supplies both upper-bound proofs;
finiteCoefficientCompositum is the supremum of intermediate fields, hence is finite. -/
theorem compositum_upper :
    (∀ E F : Padic.FiniteCoefficientFields l Ω,
      E ≤ Padic.finiteCoefficientCompositum l Ω E F) ∧
    (∀ E F : Padic.FiniteCoefficientFields l Ω,
      F ≤ Padic.finiteCoefficientCompositum l Ω E F) := by
  exact ⟨fun E F ↦ (Padic.finiteCoefficientFields_properties l Ω).1 E F |>.1,
    fun E F ↦ (Padic.finiteCoefficientFields_properties l Ω).1 E F |>.2⟩

/-- Directedness uses the actual finite compositum, not finiteness of the field as a set.
Source: common-stage formula (blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
instance coefficientDirected : IsDirectedOrder (Padic.FiniteCoefficientFields l Ω) where
  directed E F := ⟨Padic.finiteCoefficientCompositum l Ω E F,
    (compositum_upper l Ω).1 E F, (compositum_upper l Ω).2 E F⟩

end PadicCoefficients
end CategoryTheory.BilinearCoefficientDescent
