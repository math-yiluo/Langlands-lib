/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives

/-! # Actual restricted resolutions with section comparison

Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: lem-pc-restricted-resolution-sections-exist). -/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- Termwise restriction gives an injective resolution and its actual section comparison.
Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: lem-pc-restricted-resolution-sections-exist).

Proof: Exact open restriction preserves injectives by its exact left adjoint.
Apply restriction termwise, transport the single-complex augmentation along the
singleMapHomologicalComplex isomorphism, and retain the resulting complex as the
restricted resolution. The comparison of complexes is the identity. Identify each
section group using restrictAppIso and the identity U.ι_image_top. Naturality of
restrictAppIso makes these identifications a chain isomorphism. Its explicit
components verify the final field; the augmentation follows from the single
complex comparison. This constructs all data without choosing an arbitrary witness. -/
theorem restrictedResolutionSections_exists {X : Scheme.{uBC}} {F : X.Modules}
    (I : InjectiveResolution F) (U : X.Opens) :
    Nonempty (RestrictedResolutionSections I U) := by
  let R := restrictFunctor U.ι
  let : PreservesFiniteLimits (SheafOfModules.overFunctor X.ringCatSheaf U) :=
    moduleOverFunctor_limits X.toRingedSpace U
  let : PreservesFiniteColimits (SheafOfModules.overFunctor X.ringCatSheaf U) :=
    moduleOverFunctor_colimits X.toRingedSpace U
  let : PreservesFiniteLimits R := preservesFiniteLimits_of_natIso (overFunctorEquiv U)
  let : PreservesFiniteColimits R := preservesFiniteColimits_of_natIso (overFunctorEquiv U)
  let : R.Additive := Functor.additive_of_preserves_binary_products R
  let : R.PreservesInjectiveObjects :=
    { injective_obj := fun {M} hM ↦ by
        let : Injective ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M) :=
          (module_open_restriction_injectives X U).2.2.1 M hM
        exact Injective.of_iso ((overFunctorEquiv U).app M)
          ((overEquiv U).functor.injective_obj_of_injective inferInstance) }
  let e := (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℕ) 0).app F
  let J : InjectiveResolution (R.obj F) :=
    { cocomplex := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      injective := fun n ↦ R.injective_obj_of_injective (I.injective n)
      ι := e.inv ≫ (R.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
      quasiIso := by infer_instance }
  let c : ((RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{uBC}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        J.cocomplex ≅
      ((RingedSpace.openModuleSections X.toRingedSpace U).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex :=
    HomologicalComplex.Hom.isoOfComponents (fun n ↦
      (I.cocomplex.X n).restrictAppIso U.ι ⊤ ≪≫
        (I.cocomplex.X n).presheaf.mapIso (eqToIso (congrArg op U.ι_image_top))) (by
          intro i j hij
          dsimp [J, R, RingedSpace.globalSectionsFunctor, RingedSpace.openModuleSections]
          simp only [restrictAppIso, Iso.refl_hom, Category.assoc]
          exact (I.cocomplex.d i j).mapPresheaf.naturality
            ((eqToIso (congrArg op U.ι_image_top)).hom))
  refine ⟨{ resolution := J
            comparison := Iso.refl _
            augmentation := ?_
            sections := c
            components := ?_ }⟩
  · simp [J, e, R, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  · intro n
    simp [c, HomologicalComplex.Hom.isoOfComponents, Iso.refl_hom]

end AlgebraicGeometry.Scheme.Modules
