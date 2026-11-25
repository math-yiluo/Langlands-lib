/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-! # Degree-zero scalar Ext comparison

Source: Stacks Project, Cohomology, Tag 01DZ.
(blueprint: lem-sc-scalar-cohomology-ext-zero-global-sections).
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory HasExt.standard

private theorem extMk_augmentation {C : Type*} [Category C] [Abelian C] [HasExt C]
    {A B : C} (I : InjectiveResolution B) (b : A ⟶ B) :
    I.extMk (b ≫ I.ι.f 0) 1 rfl (by simp) = Abelian.Ext.mk₀ b := by
  let := HasDerivedCategory.standard C
  open CochainComplex HomComplex in
  have h : Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk (b ≫ I.ι.f 0 ≫ (I.cochainComplexXIso 0 0 rfl).inv)
        (zero_add (0 : ℤ)) 1 rfl (by simp [I.cochainComplex_d 0 1 0 1 rfl rfl])) =
      ShiftedHom.mk₀ 0 rfl ((singleFunctor C 0).map b ≫ I.ι') := by
    apply Cocycle.equivHomShift.injective
    ext : 1
    apply (Cochain.fromSingleEquiv (p := 0) (q := 0) (n := 0) rfl).injective
    simp [Cocycle.equivHomShift_apply, Cochain.fromSingleEquiv,
      Cochain.rightUnshift_v, ShiftedHom.mk₀, I.ι'_f_zero, singleFunctor,
      HomologicalComplex.single_map_f_self, CategoryTheory.shiftFunctorZero',
      CochainComplex.shiftFunctorZero_eq]
  ext
  rw [I.extMk_hom]
  simp only [Category.assoc]
  erw [h]
  simp [ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀,
    DerivedCategory.singleFunctorIsoCompQ]
  rfl

/-- The canonical degree-zero comparison represents a section by its module morphism.
Source: Stacks Project, Cohomology, Tag 01DZ.
(blueprint: lem-sc-scalar-cohomology-ext-zero-global-sections).

Proof: In an injective resolution I of F, the augmentation sends a section s to
a degree-zero cocycle. Evaluation at one identifies this cocycle with
homOfGlobalSection F s followed by the augmentation. The defining cocycle formula
for moduleExtEquiv and the degree-zero Ext augmentation identity identify its Ext
class with mk₀ of homOfGlobalSection F s. The degree-zero derived comparison is
the inverse of the augmentation on sections. Finally restriction of scalars sends
mk₀ to mk₀ and composition with the scalar unit sends this to the displayed class.
This argument also applies to zero sections and empty schemes. -/
theorem scalarCohomologyExtEquiv_zero_globalSections
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules)
    (a : scalarCohomology f F 0) :
    scalarCohomologyExtEquiv f F 0 a =
      Abelian.Ext.mk₀ (scalarUnitMorphism f ≫
        scalarHom f (homOfGlobalSection F (scalarGlobalSectionsEquiv f F a))) := by
  classical
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : HasExt.{w} X.Modules :=
    hasExt_of_enoughInjectives.{w, w, w + 1} X.Modules
  let : EnoughInjectives (SheafOfModules.{w} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : EnoughInjectives (SheafOfModules.{w} X.ringCatSheaf) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : HasExt.{w} (SheafOfModules.{w} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives.{w, w, w + 1} (SheafOfModules.{w} X.ringCatSheaf)
  let I : InjectiveResolution F := InjectiveResolution.of F
  let S := RingedSpace.globalSectionsFunctor.{w} X.toRingedSpace
  let : S.Additive := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let : PreservesFiniteLimits S :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))
  let s := scalarGlobalSectionsEquiv f F a
  let c := (I.toRightDerivedZero' S).hom s
  have hc : (homOfGlobalSection F s ≫ I.ι.f 0).val.app (op ⊤) (1 : Γ(X, ⊤)) =
      (RingedSpace.globalSectionsComplex I).iCycles 0 c := by
    change Hom.app (I.ι.f 0) ⊤
      (Hom.app (homOfGlobalSection F s) ⊤ (1 : Γ(X, ⊤))) = _
    rw [homOfGlobalSection_app_one, presheaf_map_id_apply]
    exact (ConcreteCategory.congr_hom (I.toRightDerivedZero'_comp_iCycles S) s).symm
  have ha : a = (I.isoRightDerivedObj S 0).inv
      ((RingedSpace.globalSectionsComplex I).homologyπ 0 c) := by
    have h := ConcreteCategory.congr_hom (S.rightDerivedZeroIsoSelf_hom_inv_id_app F) a
    change S.toRightDerivedZero.app F (S.rightDerivedZeroIsoSelf.hom.app F a) = a at h
    rw [I.toRightDerivedZero_eq] at h
    exact h.symm
  have hm : moduleExtEquiv F 0 a = Abelian.Ext.mk₀.{w} (homOfGlobalSection F s) := by
    unfold moduleExtEquiv
    rw [ha, (Classical.choose_spec (exists_moduleExtEquiv F 0)) I c
      (homOfGlobalSection F s ≫ I.ι.f 0) (by simp) hc]
    exact extMk_augmentation I (homOfGlobalSection F s)
  unfold scalarCohomologyExtEquiv scalarCohomologyExtMap scalarExtMap
  change (Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
    ((moduleExtEquiv F 0 a).mapExactFunctor (scalarFunctor f)) (zero_add 0) = _
  rw [hm, Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  rfl

end
end AlgebraicGeometry.Scheme.Modules
