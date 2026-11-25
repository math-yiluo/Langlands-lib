/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives

/-! # FlatBaseChangeOpenChoicesExist

Source: Stacks Project, Cohomology, Tags 02N7, 01FB and 01E4.
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

private theorem restrictedResolutionSections_nonempty {X : Scheme.{uBC}} {F : X.Modules}
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

/-- Compatible restricted resolutions and the restricted adjunction unit exist.
Source: Stacks, Cohomology, Tags 01E1, 01FB, 01E4; Modules, Tag 01AJ.
(blueprint: lem-weil-pbc-flat-base-change-open-choices-exist).

Proof: Restrict I and J termwise to U = f⁻¹V and W = g'⁻¹U. Restriction is exact
 and preserves injectives: transport the overFunctor results across
 overFunctorEquiv, as in module_sections_acyclic_of_cohomology_vanishing. Thus
 the restricted augmentations give resolutions of the restricted modules.
 Identify sections using restrictAppIso, evaluated at
 the top open, followed by the equality that the inclusion maps the top to U
 (respectively W). These identifications satisfy the specified components.
 Restrict the original pullback unit to U and transpose across restriction's
 adjunction to define psi. On an open T in U, the unit sends m to 1 tensor m;
 restricting the original unit gives the same map on h⁻¹T. With the canonical
 pushforward composition identifications this is exactly unit_square. Bundle
 these choices to obtain the required inhabitant. -/
theorem flatBaseChangeMap_sections_choices {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] (F : X.Modules) :
    ∀ (I : InjectiveResolution F)
      (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)) (V : S.Opens),
      Nonempty (FlatBaseChangeOpenChoices f g F I J V) := by
  intro I J V
  let U := f ⁻¹ᵁ V
  let h := pullback.snd g f
  let W := h ⁻¹ᵁ U
  let r := h.resLE U W le_rfl
  let F' := (tensorPullback h).obj F
  let E : pushforward r ⋙ pushforward U.ι ≅ pushforward (W.ι ≫ h) :=
    pushforwardComp r U.ι ≪≫ pushforwardCongr (h.resLE_comp_ι le_rfl)
  let a : F ⟶ (pushforward (W.ι ≫ h)).obj ((restrictFunctor W.ι).obj F') :=
    (Classical.choose (exists_tensorPullbackAdjunction h)).unit.app F ≫
      (pushforward h).map ((restrictAdjunction W.ι).unit.app F') ≫
        (pushforwardComp W.ι h).hom.app ((restrictFunctor W.ι).obj F')
  let psi := ((restrictAdjunction U.ι).homEquiv _ _).symm
    (a ≫ E.inv.app ((restrictFunctor W.ι).obj F'))
  obtain ⟨source⟩ := restrictedResolutionSections_nonempty I U
  obtain ⟨target⟩ := restrictedResolutionSections_nonempty J W
  refine ⟨{ psi := psi, source := source, target := target, unit_square := ?_ }⟩
  change (restrictAdjunction U.ι).unit.app F ≫ (pushforward U.ι).map psi ≫
    (pushforwardComp r U.ι).hom.app _ ≫
      (pushforwardCongr (h.resLE_comp_ι le_rfl)).hom.app _ = a
  have hp := ((restrictAdjunction U.ι).homEquiv _ _).apply_symm_apply
    (a ≫ E.inv.app ((restrictFunctor W.ι).obj F'))
  rw [Adjunction.homEquiv_unit] at hp
  change ((restrictAdjunction U.ι).unit.app F ≫ (pushforward U.ι).map psi) ≫
    E.hom.app _ = a
  rw [hp]
  simp


end AlgebraicGeometry.Scheme.Modules
