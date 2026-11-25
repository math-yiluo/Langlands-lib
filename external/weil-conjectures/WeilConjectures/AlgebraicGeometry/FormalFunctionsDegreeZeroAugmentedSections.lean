/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Ext


public import WeilConjectures.AlgebraicGeometry.FormalFibreCohomology
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.BasicPropertiesDegreeZero
import WeilConjectures.AlgebraicGeometry.ResolutionSectionClassZeroAugmentation
import WeilConjectures.AlgebraicGeometry.TensorUnitOpenDegreeZero
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation
import WeilConjectures.AlgebraicGeometry.SchemeModulesEnoughInjectives
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-! # Canonical theta on augmented sections

Source: Stacks Project, Cohomology, Tags 01E4 and 01FB, degree-zero formulas.
(blueprint: lem-weil-pbc-formal-functions-degree-zero-augmented-sections).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry


namespace Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictedResolutionSections_nonempty {X : Scheme.{u}} {F : X.Modules}
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
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem openChoices_nonempty {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (F : X.Modules) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)) (V : S.Opens) :
    Nonempty (FlatBaseChangeOpenChoices f g F I J V) := by
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem wholeOpen_zero_injective {X : Scheme.{u}} (U : X.Opens)
    (hU : (⊤ : X.Opens) ≤ U) (F : X.Modules) :
    Function.Injective (moduleCohomologyFMap U.ι
      ((restrictAdjunction U.ι).unit.app F) 0) := by
  have hu : U = ⊤ := le_antisymm le_top hU
  subst U
  let φ := (restrictAdjunction (⊤ : X.Opens).ι).unit.app F
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  have hs : IsIso ((forget₂ _ AddCommGrpCat.{u}).map (S.map φ)) := by
    change IsIso (Hom.app φ ⊤)
    dsimp only [φ]
    rw [restrictAdjunction_unit_app_app]
    have ht : (⊤ : X.Opens).ι ''ᵁ ((⊤ : X.Opens).ι ⁻¹ᵁ (⊤ : X.Opens)) = ⊤ := by
      simp
    have hh : homOfLE ((⊤ : X.Opens).ι.image_preimage_le ⊤) = (eqToIso ht).hom :=
      Subsingleton.elim _ _
    rw [hh]
    infer_instance
  obtain ⟨eG, eF, he⟩ := moduleCohomologyFMap_basic_degree_zero (⊤ : X.Opens).ι φ
  have hm : IsIso (moduleCohomologyFMap (⊤ : X.Opens).ι φ 0) := by
    exact IsIso.of_isIso_fac_right he.symm
  exact (ConcreteCategory.bijective_of_isIso
    (moduleCohomologyFMap (⊤ : X.Opens).ι φ 0)).injective

end Scheme.Modules



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stalkMap_germ {Y : Scheme.{u}} (y : Y) {M N : Y.Modules}
    (a : M ⟶ N) (V : Y.Opens) (hy : y ∈ V) (t : M.presheaf.obj (op V)) :
    TopCat.Presheaf.germ N.presheaf V y hy (Scheme.Modules.Hom.app a V t) =
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map a).hom
        (TopCat.Presheaf.germ M.presheaf V y hy t) := by
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy a.mapPresheaf t).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Explicit resolution comparisons require additional elaboration steps.
/-- A canonical theta sends the fixed direct-image augmentation of a germ of a section
of any module to the global-sections augmentation of its tensor-pullback unit image.
Source: Stacks Project, Cohomology, Tags 01E4 and 01FB (degree zero).
(blueprint: lem-weil-pbc-formal-functions-degree-zero-augmented-sections).

Proof: Choose an injective resolution I of F and a resolution J of its tensor
pullback F'. Restrict these termwise to U = f inverse V and W = i_n inverse U.
Restriction is exact and preserves injectives, so these give the restricted
resolutions in FlatBaseChangeOpenChoices. Define psi by restricting the tensor
adjunction unit and transposing under the restriction adjunction; functoriality
of pushforward gives its unit square. No flatness of i_n is used. Identify
sections by restrictAppIso and the inclusion-image-top equality.
Augment the restriction of t to U by the global-sections toRightDerivedZero map,
obtaining xi. Express this map using InjectiveResolution.toRightDerivedZero_eq.
The augmentation and component equations of the restricted resolution identify
the resulting zero-cycle with I's augmentation of t on U. The section class
map takes this cycle to its homology-sheaf class by the sheafification counit;
its composite with the inverse resolution comparison is thus the direct-image
augmentation of t on V. Naturality of germs identifies its germ with the stalk
augmentation applied to germ(t). Apply IsFormalFunctionsTheta to xi.
The zero-augmentation square for the cohomology h-map of psi identifies the
right side with the augmented restriction of the original tensor-unit image
of t, by the unit square. The inequality hV identifies W with top. On this
open the restriction of sections is an isomorphism, as are the degree-zero
augmentation maps, so the degree-zero cohomology restriction is injective.
Cancel it to get the claimed equality. Empty fibres, the zero module and t=0
are covered by the same augmentation identities. -/
theorem formalFunctions_degreeZero_augmented_sections {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) (F : X.Modules) (n : ℕ)
    (θ : formalFunctionsStalk f y F 0 →ₗ[Y.presheaf.stalk y]
      formalFibreCohomologyLocal f y F 0 n)
    (hθ : IsFormalFunctionsTheta f y F 0 n θ)
    (V : Y.Opens) (hy : y ∈ V)
    (hV : (⊤ : (formalFibre f y n).Opens) ≤
      (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V))
    (t : F.presheaf.obj (op (f ⁻¹ᵁ V))) :
    θ (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app F)).hom
        (TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj F).val.presheaf
          V y hy t)) =
    ((RingedSpace.globalSectionsFunctor (formalFibre f y n).toRingedSpace).toRightDerivedZero.app
        ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)).hom
      (((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F).presheaf.map
        (homOfLE hV).op
          ((((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
            (formalFibreι f y n))).unit.app F).val.app (op (f ⁻¹ᵁ V))).hom t)) := by
  let : EnoughInjectives X.Modules := Scheme.Modules.enoughInjectives (X := X)
  let : EnoughInjectives (formalFibre f y n).Modules :=
    Scheme.Modules.enoughInjectives (X := formalFibre f y n)
  have I := injectiveResolution F
  have J := injectiveResolution ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)
  obtain ⟨D⟩ := Scheme.Modules.openChoices_nonempty f (formalFibreBaseMap Y y n) F I J V
  let s := (F.restrictAppIso (f ⁻¹ᵁ V).ι ⊤).inv
    (F.presheaf.map (eqToHom (f ⁻¹ᵁ V).ι_image_top).op t)
  let xi := ((RingedSpace.globalSectionsFunctor
    (f ⁻¹ᵁ V).toScheme.toRingedSpace).toRightDerivedZero.app
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).hom s
  have hx := Scheme.Modules.resolutionSectionClass_zero_augmentation f F I V D.source s
  have hs : F.presheaf.map (eqToHom (f ⁻¹ᵁ V).ι_image_top.symm).op
      ((F.restrictAppIso (f ⁻¹ᵁ V).ι ⊤).hom s) = t := by
    dsimp only [s]
    rw [Iso.inv_hom_id_apply, ← Functor.map_comp_apply]
    simp
  rw [hs] at hx
  have he := hθ I J V hy D xi
  have hg := congrArg (fun z ↦ TopCat.Presheaf.germ
    (((Scheme.Modules.pushforward f).rightDerived 0).obj F).presheaf V y hy z) hx
  have hg' := stalkMap_germ y
    ((Scheme.Modules.pushforward f).toRightDerivedZero.app F) V hy t
  have hg'' := hg.trans hg'
  have hinj := Scheme.Modules.wholeOpen_zero_injective
    ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) hV
    ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)
  have hc := congrArg (fun z ↦ Scheme.Modules.moduleCohomologyFMap
    ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
      ((Scheme.Modules.restrictAdjunction
        ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)) 0 (θ z)) hg''.symm
  have ht := Scheme.Modules.tensorUnit_open_degree_zero f
    y n F I J V D hV t
  apply hinj
  exact Eq.trans hc (Eq.trans he ht)

end AlgebraicGeometry
