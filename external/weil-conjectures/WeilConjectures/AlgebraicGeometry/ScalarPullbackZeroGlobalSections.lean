/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison

/-! # Pullback in degree zero on global sections

Source: Stacks Project, Cohomology, Tags 01DZ, 0FKV; Modules, Tag 0096.
(blueprint: lem-sc-scalar-pullback-zero-global-sections).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

noncomputable section
private local instance {k : Type w} [Field k] {X : Scheme.{w}} :
    MonoidalCategory (KSheaf X k) := Sheaf.monoidalCategory _ _

private local instance {k : Type w} [Field k] {X : Scheme.{w}} :
    HasExt.{w + 1} (KSheaf X k) := HasExt.standard _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem section_representative {X : Scheme.{w}} (F : SheafOfModules.{w} X.ringCatSheaf)
    (s : F.val.obj (op ⊤)) :
    ∃ φ : SheafOfModules.unit X.ringCatSheaf ⟶ F,
      φ.val.app (op ⊤) (1 : Γ(X, ⊤)) = s := by
  let t : F.sections := PresheafOfModules.sectionsMk
    (fun U ↦ F.val.map (homOfLE (le_top (a := U.unop))).op s) (by
      intro U V i
      change F.val.presheaf.map i (F.val.presheaf.map
        (homOfLE (le_top (a := U.unop))).op s) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  refine ⟨F.unitHomEquiv.symm t, ?_⟩
  have ht := congrArg (fun z : F.sections ↦ z.val (op ⊤))
    (F.unitHomEquiv.apply_symm_apply t)
  change _ = F.val.map (𝟙 (op ⊤)) s at ht
  rw [F.val.map_id] at ht
  exact ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_ext_section {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F : SheafOfModules.{w} X.ringCatSheaf)
    (x : scalarCohomology f F 0) :
    ∃ φ : SheafOfModules.unit X.ringCatSheaf ⟶ F,
      φ.val.app (op ⊤) (1 : Γ(X, ⊤)) = scalarGlobalSectionsEquiv f F x ∧
      scalarCohomologyExtEquiv f F 0 x =
        Abelian.Ext.mk₀ (scalarUnitMorphism f ≫ scalarHom f φ) := by
  classical
  let : EnoughInjectives (SheafOfModules.{w} X.ringCatSheaf) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : HasExt.{w} (SheafOfModules.{w} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives.{w, w, w + 1} _
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : PreservesFiniteLimits S :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))
  obtain ⟨φ, hφ⟩ := section_representative F (scalarGlobalSectionsEquiv f F x)
  refine ⟨φ, hφ, ?_⟩
  let : HasInjectiveResolution F :=
    inferInstanceAs (HasInjectiveResolution (show SheafOfModules.{w} X.ringCatSheaf from F))
  have : S.Additive := RingedSpace.globalSectionsFunctor_additive _
  let I := injectiveResolution F
  let s := scalarGlobalSectionsEquiv f F x
  let z := (I.toRightDerivedZero' S).hom s
  have hz : (φ ≫ I.ι.f 0).val.app (op ⊤) (1 : Γ(X, ⊤)) =
      (RingedSpace.globalSectionsComplex I).iCycles 0 z := by
    change (I.ι.f 0).val.app (op ⊤) (φ.val.app (op ⊤) (1 : Γ(X, ⊤))) = _
    rw [hφ]
    exact (ConcreteCategory.congr_hom (I.toRightDerivedZero'_comp_iCycles S) s).symm
  have he := Classical.choose_spec (exists_moduleExtEquiv F 0) I z (φ ≫ I.ι.f 0)
    (by simp) hz
  have hc : x = (I.isoRightDerivedObj S 0).inv
      ((RingedSpace.globalSectionsComplex I).homologyπ 0 z) := by
    have hs : S.toRightDerivedZero.app F s = x := by
      change (S.rightDerivedZeroIsoSelf.app F).inv
        ((S.rightDerivedZeroIsoSelf.app F).hom x) = x
      exact ConcreteCategory.congr_hom ((S.rightDerivedZeroIsoSelf.app F).hom_inv_id) x
    rw [← hs, I.toRightDerivedZero_eq S]
    rfl
  have hm : moduleExtEquiv F 0 x = Abelian.Ext.mk₀ φ := by
    unfold moduleExtEquiv
    rw [hc, he]
    exact extMk_augmentation I φ
  unfold scalarCohomologyExtEquiv scalarCohomologyExtMap scalarExtMap
  change (Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
    ((moduleExtEquiv F 0 x).mapExactFunctor (scalarFunctor f)) (zero_add 0) = _
  rw [hm, Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.MonoidalCategory in
private theorem scalar_ext_evaluation {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F : SheafOfModules.{w} X.ringCatSheaf)
    (x : scalarCohomology f F 0)
    (μ : 𝟙_ (KSheaf X k) ⟶ scalarSheaf f F)
    (hμ : scalarCohomologyExtEquiv f F 0 x = Abelian.Ext.mk₀ μ) :
    ((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{w} k)
      isTerminalTop).homEquiv _ _
        (constantScalarUnitIso.hom ≫ μ)) (1 : k) = scalarGlobalSectionsEquiv f F x := by
  obtain ⟨φ, hφ, hx⟩ := scalar_ext_section f F x
  have hm : scalarUnitMorphism f ≫ scalarHom f φ = μ :=
    (Abelian.Ext.mk₀_bijective _ _).injective (hx.symm.trans hμ)
  rw [← hm]
  unfold scalarUnitMorphism
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  change φ.val.app (op ⊤) (scalarMap f ⊤ 1) = _
  rw [(scalarMap f ⊤).map_one]
  exact hφ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homEquiv_unique {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    (c : C) (d : D) (v : F'.obj c ⟶ d) :
    a.homEquiv c d ((a.leftAdjointUniq b).hom.app c ≫ v) = b.homEquiv c d v := by
  rw [a.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    b.homEquiv_unit]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degree-zero cohomology pullback evaluates to the tensor-pullback unit on sections.
Source: Stacks Project, Cohomology, Tags 01DZ, 0FKV; Modules, Tag 0096.
(blueprint: lem-sc-scalar-pullback-zero-global-sections).

Proof: The cocycle formula specifying moduleExtEquiv in degree zero identifies
the rightDerivedZeroIsoSelf global section with evaluation at 1 of the unique
morphism from the structure sheaf representing the degree-zero Ext class.
After restriction of scalars and precomposition with scalarUnitMorphism, the
constant-sheaf adjunction identifies the resulting scalar-unit morphism with
that same global section. Represent scalarCohomologyExtEquiv f F 0 x by mk₀
of this morphism. Exact inverse image sends mk₀ to the degree-zero class of
its inverse-image morphism, and composing with mk₀ classes is ordinary morphism
composition. Precomposition with scalarInverseUnitIso.inv identifies the
inverse-image constant unit with the target constant unit. Postcomposition with
scalarPullbackCoefficient is adjoint to the sectionwise tensor-pullback unit,
by Classical.choose_spec of exists_scalarPullbackCoefficient. Apply that
adjunction identity to the top open. Its inverse image is the top open on Y;
the restriction along the canonical inclusion of the top open into its inverse
image is the one in tensorPullbackTopSection. Finally cancel the target
scalarCohomologyExtEquiv with its inverse in scalarCohomologyPullback. No
quasi-coherence or nonemptiness is used, and the formula sends zero to zero. -/
theorem scalarCohomologyPullback_zero_globalSections
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : X.Modules) (x : scalarCohomology f F 0) :
    scalarGlobalSectionsEquiv g ((tensorPullback a).obj F)
        (scalarCohomologyPullback f g a h F 0 x) =
      tensorPullbackTopSection a F (scalarGlobalSectionsEquiv f F x) := by
  classical
  let cX := constantSheafAdj (Opens.grothendieckTopology X)
    (ModuleCat.{w} k) isTerminalTop
  let cY := constantSheafAdj (Opens.grothendieckTopology Y)
    (ModuleCat.{w} k) isTerminalTop
  let adj := (TopologicalSpace.Opens.map a.base).sheafAdjunctionContinuous
    (ModuleCat.{w} k) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y)
  let e := ((TopologicalSpace.Opens.map a.base).constantSheafsheafPullbackIso
    (ModuleCat.{w} k) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) isTerminalTop isTerminalTop).app (ModuleCat.of k k)
  let b := (cX.comp adj).ofNatIsoRight
    ((TopologicalSpace.Opens.map a.base).sheafPushforwardContinuousCompSheafSectionsObjIso
      (ModuleCat.{w} k) (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) (op ⊤))
  obtain ⟨φ, hφ, hx⟩ := scalar_ext_section f F x
  let μ := scalarUnitMorphism f ≫ scalarHom f φ
  let ν := (scalarInverseUnitIso (k := k) a).inv ≫
    (scalarInverseImage a).map μ ≫ scalarPullbackCoefficient f g a h F
  have hν : scalarCohomologyExtEquiv g ((tensorPullback a).obj F) 0
      (scalarCohomologyPullback f g a h F 0 x) = Abelian.Ext.mk₀ ν := by
    unfold scalarCohomologyPullback
    rw [AddEquiv.apply_symm_apply, hx, Abelian.Ext.mapExactFunctor_mk₀,
      Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀]
    rfl
  rw [← scalar_ext_evaluation g ((tensorPullback a).obj F) _ ν hν]
  have hc : constantScalarUnitIso.hom ≫ ν =
      e.inv ≫ (scalarInverseImage a).map (constantScalarUnitIso.hom ≫ μ) ≫
        scalarPullbackCoefficient f g a h F := by
    dsimp only [ν]
    unfold scalarInverseUnitIso
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Functor.map_comp,
      Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  rw [hc]
  have he : cY.homEquiv _ _
      (e.inv ≫ (scalarInverseImage a).map (constantScalarUnitIso.hom ≫ μ) ≫
        scalarPullbackCoefficient f g a h F) =
      b.homEquiv _ _ ((scalarInverseImage a).map (constantScalarUnitIso.hom ≫ μ) ≫
        scalarPullbackCoefficient f g a h F) := by
    have hh := homEquiv_unique b cY (ModuleCat.of k k)
      (scalarSheaf g ((tensorPullback a).obj F))
      (e.inv ≫ (scalarInverseImage a).map (constantScalarUnitIso.hom ≫ μ) ≫
        scalarPullbackCoefficient f g a h F)
    change b.homEquiv _ _ (e.hom ≫ (e.inv ≫
      (scalarInverseImage a).map (constantScalarUnitIso.hom ≫ μ) ≫
        scalarPullbackCoefficient f g a h F)) = _ at hh
    simp only [Iso.hom_inv_id_assoc] at hh
    exact hh.symm
  rw [he]
  change (cX.homEquiv _ _ (adj.homEquiv _ _
    ((scalarInverseImage a).map (constantScalarUnitIso.hom ≫ μ) ≫
      scalarPullbackCoefficient f g a h F))) (1 : k) = _
  erw [adj.homEquiv_naturality_left, cX.homEquiv_naturality_right]
  have hμ : (cX.homEquiv _ _ (constantScalarUnitIso.hom ≫ μ)) (1 : k) =
      scalarGlobalSectionsEquiv f F x := scalar_ext_evaluation f F x μ hx
  change ((adj.homEquiv _ _ (scalarPullbackCoefficient f g a h F)).hom.app (op ⊤))
    ((cX.homEquiv _ _ (constantScalarUnitIso.hom ≫ μ)) (1 : k)) = _
  rw [hμ]
  have hj : ((adj.homEquiv _ _ (scalarPullbackCoefficient f g a h F)).hom.app (op ⊤))
      (scalarGlobalSectionsEquiv f F x) =
      ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F).val.app
        (op ⊤) (scalarGlobalSectionsEquiv f F x) := by
    simpa only [scalarPullbackCoefficient, adj] using
      Classical.choose_spec (exists_scalarPullbackCoefficient f g a h F)
        ⊤ (scalarGlobalSectionsEquiv f F x)
  rw [hj]
  unfold tensorPullbackTopSection
  change _ = ((tensorPullback a).obj F).val.map (𝟙 (op ⊤)) _
  simp

end

end AlgebraicGeometry.Scheme.Modules
