/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Flat resolutions of `𝒪_X`-modules

The symmetric monoidal closed category `X.Modules` of `𝒪_X`-modules is monoidal preadditive and
admits functorial flat resolutions (`CategoryTheory.Abelian.HasFunctorialFlatResolution`): it has
a flat separator, the coproduct over the opens `U` of `X` of the sheafified free modules
`𝒪_X[U]` on the representable presheaves. Tensoring with the sheafification `a P` of a presheaf
of modules `P` is `M ↦ a (P ⊗ M)`, which is left exact if every `P(V)` is a flat
`𝒪_X(V)`-module; for `P` the free presheaf of modules on `U`, each `P(V)` is free.

These are the hypotheses under which the K-flat machinery defines left derived functors on the
unbounded derived category `D(𝒪_X)`
(`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

instance (M : X.Modules) : (tensorRight M).Additive :=
  Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight M)

/-- The tensor product of `𝒪_X`-modules is additive in each variable: tensoring with a fixed
module is a left adjoint. -/
instance : MonoidalPreadditive X.Modules where
  whiskerLeft_zero {M _ _} := (tensorLeft M).map_zero _ _
  zero_whiskerRight {M _ _} := (tensorRight M).map_zero _ _
  whiskerLeft_add {M _ _} _ _ := (tensorLeft M).map_add
  add_whiskerRight {M _ _} _ _ := (tensorRight M).map_add

attribute [local instance] presheafMonoidalCategory sheafificationMonoidal

/-- Tensoring with the sheafification `a P` of a presheaf of modules is, up to isomorphism, the
sheafification of the tensor product of presheaves with `P`. -/
noncomputable def tensorLeftSheafificationIso
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    tensorLeft ((sheafification X).obj P) ≅
      forgetToPresheafOfModules X ⋙ tensorLeft P ⋙ sheafification X :=
  have : IsIso (sheafificationAdjunction X).counit :=
    (inferInstance : IsIso (_root_.PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 X.ringCatSheaf.obj)).counit)
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction X).counit).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (forgetToPresheafOfModules X)
      (NatIso.ofComponents (fun Q ↦ Functor.Monoidal.μIso (sheafification X) P Q)
        (fun _ ↦ by simp))

/-- A functor to presheaves of modules preserves finite limits as soon as all its composites
with the evaluation functors do. -/
lemma _root_.PresheafOfModules.preservesFiniteLimits_of_evaluation {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {D : Type*} [Category D] (G : D ⥤ _root_.PresheafOfModules.{u} R)
    (h : ∀ V, PreservesFiniteLimits (G ⋙ _root_.PresheafOfModules.evaluation R V)) :
    PreservesFiniteLimits G where
  preservesFiniteLimits _ _ _ := ⟨fun {_} ↦ ⟨fun {_} hc ↦ ⟨
    _root_.PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun V ↦
      isLimitOfPreserves (G ⋙ _root_.PresheafOfModules.evaluation R V) hc⟩⟩⟩

/-- The sheafification of a presheaf of modules with flat values is flat. -/
lemma flat_sheafification_obj (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)
    (hP : ∀ V, Module.Flat Γ(X, V.unop) (P.obj V)) :
    ObjectProperty.flat ((sheafification X).obj P) := by
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have : PreservesFiniteLimits (tensorLeft P) :=
    _root_.PresheafOfModules.preservesFiniteLimits_of_evaluation _ fun V ↦ by
      let P' : ModuleCat.{u} Γ(X, V.unop) := P.obj V
      have : PreservesFiniteLimits (tensorLeft P') :=
        (ObjectProperty.flat_iff_preservesFiniteLimits _).1
          ((ModuleCat.flat_iff_flat P').2 (hP V))
      exact ⟨fun J _ _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨isLimitOfPreserves (tensorLeft P')
        (isLimitOfPreserves (_root_.PresheafOfModules.evaluation X.ringCatSheaf.obj V) hc)⟩⟩⟩⟩
  have : PreservesFiniteLimits (forgetToPresheafOfModules X) :=
    have := (sheafificationAdjunction X).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  have : PreservesFiniteLimits (sheafification X) :=
    inferInstanceAs (PreservesFiniteLimits
      (_root_.PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj)))
  have : PreservesFiniteLimits (forgetToPresheafOfModules X ⋙ tensorLeft P ⋙
      sheafification X) := by
    have := comp_preservesFiniteLimits (tensorLeft P) (sheafification X)
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (tensorLeftSheafificationIso P).symm

/-- The sheafified free module `𝒪_X[U]` on the presheaf represented by an open `U` is flat. -/
lemma flat_sheafification_free_yoneda (U : X.Opens) :
    ObjectProperty.flat ((sheafification X).obj
      ((_root_.PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U))) :=
  flat_sheafification_obj _ fun V ↦
    inferInstanceAs (Module.Flat Γ(X, V.unop) ((V.unop ⟶ U) →₀ Γ(X, V.unop)))

/-- `X.Modules` has a flat separator: the coproduct of the sheafified free modules `𝒪_X[U]`. -/
theorem exists_flat_separator (X : Scheme.{u}) :
    ∃ G : X.Modules, IsSeparator G ∧ ObjectProperty.flat G :=
  have : IsGrothendieckAbelian.{u} X.Modules :=
    SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  ⟨_, (SheafOfModules.isSeparating_sheafification_freeYoneda
      X.ringCatSheaf).isSeparator_coproduct,
    ObjectProperty.flat_coproduct _ fun U ↦ flat_sheafification_free_yoneda U⟩

/-- `𝒪_X`-modules admit functorial flat resolutions: `X.Modules` has a flat separator. -/
instance hasFunctorialFlatResolution (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution X.Modules :=
  have : IsGrothendieckAbelian.{u} X.Modules :=
    SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  (Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator _).2 (exists_flat_separator X)

end AlgebraicGeometry.Scheme.Modules
