/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.ScalarInternalHomData
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Adjunction.Opposites
import WeilConjectures.CategoryTheory.DerivedSectionScalarTransport
/-! # Scalar adjunctions under section reconstruction

Source: Stacks Project, Modules on Sites, Tags 03EK and 0GMW; Cohomology on Sites,
Tags 06YS, 06YY and 07A6; Derived Categories, Tag 09T5; blueprint main-20261015,
det-prop-scalar-six-pullback.proof.md, (1), first paragraph
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u c v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

-- Upstream made these instances local (InternalSectionTensorComparison, SheafTensor).
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance] sfbSheafTensor_monoidalPreadditive sfbSheafTensor_hasWeakSheafify
attribute [instance] SheafOfModules.ScalarDerivedPair.extension_additive

namespace CategoryTheory.InternalAbelianSheafModule

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max c v, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]

/-- The section-ring map reconstructed from the specified internal ring map.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
def sectionScalarMap {R S : Sheaf J AddCommGrpCat.{u}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] : sectionRingSheaf J R ⟶ sectionRingSheaf J S :=
  ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence Cᵒᵖ AddCommGrpCat.{u}).functor.map
      ((sheafToPresheaf J AddCommGrpCat.{u}).mapCommMon.map
        (CommMon.homMk (A := CommMon.mk R) (B := CommMon.mk S) (Mon.Hom.mk' a)))) commMonToRing⟩

variable {R S : Sheaf J AddCommGrpCat.{u}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]

/-- Internal modules for the scalar comparison; this is the recorded module category.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
abbrev scalarInternalModules (T : Sheaf J AddCommGrpCat.{u}) [MonObj T] :=
  Mod (Sheaf J AddCommGrpCat.{u}) T

variable [HasDerivedCategory.{w} (scalarInternalModules J R)]
  [HasDerivedCategory.{w} (scalarInternalModules J S)]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J R))]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J S))]

open SheafOfModules

private noncomputable def scalarRestrictionIso :
    Mod.comap a ⋙ (sectionModuleEquivalence J R).functor ≅
      (sectionModuleEquivalence J S).functor ⋙
        SheafOfModules.scalarRestriction (sectionScalarMap J a) := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · let h : ∀ (U : Cᵒᵖ) (r : R.obj.obj U) (x : N.X.obj.obj U),
        (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) R N.X).app U) ≫
          ((a ▷ N.X).hom.app U) ≫ ((Mod.act N.X).hom.app U)) (r ⊗ₜ[ℤ] x) =
        (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) S N.X).app U) ≫
          ((Mod.act N.X).hom.app U)) ((a.hom.app U r) ⊗ₜ[ℤ] x) := by
      intro U r x
      have hμ := congr_app (Functor.LaxMonoidal.μ_natural_left
        (sheafToPresheaf J AddCommGrpCat.{u}) a N.X) U
      have hh := ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f ≫ (Mod.act N.X).hom.app U) hμ) (r ⊗ₜ[ℤ] x)
      exact hh.symm
    let f : ((sectionModuleEquivalence J R).functor.obj ((Mod.comap a).obj N)) ⟶
        (SheafOfModules.scalarRestriction (sectionScalarMap J a)).obj
          ((sectionModuleEquivalence J S).functor.obj N) :=
      ⟨{ app := fun U ↦ ModuleCat.ofHom
          (X := ((sectionModuleEquivalence J R).functor.obj ((Mod.comap a).obj N)).val.obj U)
          (Y := ((SheafOfModules.scalarRestriction (sectionScalarMap J a)).obj
            ((sectionModuleEquivalence J S).functor.obj N)).val.obj U)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun r x ↦ h U r x }
         naturality := by intros; ext x; rfl }⟩
    let g : (SheafOfModules.scalarRestriction (sectionScalarMap J a)).obj
          ((sectionModuleEquivalence J S).functor.obj N) ⟶
        ((sectionModuleEquivalence J R).functor.obj ((Mod.comap a).obj N)) :=
      ⟨{ app := fun U ↦ ModuleCat.ofHom
          (X := ((SheafOfModules.scalarRestriction (sectionScalarMap J a)).obj
            ((sectionModuleEquivalence J S).functor.obj N)).val.obj U)
          (Y := ((sectionModuleEquivalence J R).functor.obj ((Mod.comap a).obj N)).val.obj U)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun r x ↦ (h U r x).symm }
         naturality := by intros; ext x; rfl }⟩
    exact ⟨f, g, by ext U x; rfl, by ext U x; rfl⟩
  · intro N N' f
    ext U x
    rfl

omit [UnivLE.{max c v, u}] in
private theorem inverseMate_isIso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {U : B ⥤ A} {F : D ⥤ E} {V : E ⥤ D}
    {G : A ⥤ D} {H : B ⥤ E} [G.IsEquivalence] [H.IsEquivalence]
    (adj : L ⊣ U) (adj' : F ⊣ V) (β : U ⋙ G ≅ H ⋙ V) :
    IsIso (((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ β.hom))) := by
  let α := ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ β.hom))
  let βop : TwoSquare H.op U.op V.op G.op := TwoSquare.mk _ _ _ _ (NatTrans.op β.hom)
  have hi := isIso_mateEquiv_of_isEquivalence adj.op adj'.op βop
  have he : (NatTrans.op α) = (mateEquiv adj.op adj'.op βop) := by
    ext X
    simp [α, βop, mateEquiv]
  have : IsIso (NatTrans.op α) := by rw [he]; exact hi
  have (X : A) : IsIso (α.app X) := by
    have hX : IsIso ((α.app X).op) :=
      NatIso.isIso_app_of_isIso (NatTrans.op α) (Opposite.op X)
    exact isIso_of_op (α.app X)
  exact NatIso.isIso_of_isIso_app α

end CategoryTheory.InternalAbelianSheafModule

namespace CategoryTheory.InternalAbelianSheafModule

section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max c v, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
variable {R S : Sheaf J AddCommGrpCat.{u}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
attribute [local instance] sfbSheafTensor_monoidalPreadditive sfbSheafTensor_hasWeakSheafify


/-- The balanced generator in internal coequalizer extension.
Source: Stacks 03EK (blueprint: lem-sfb-internal-section-scalar-adjunction). -/
def internalScalarGenerator (M : Mod (Sheaf J AddCommGrpCat.{u}) R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (m : M.X.obj.obj U) :
    ((Mod.extendScalars a).obj M).X.obj.obj U :=
  ((Mod.extendπ a M).hom.app U)
    (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) S M.X).app U)
      (s ⊗ₜ[ℤ] m))

end

end CategoryTheory.InternalAbelianSheafModule

namespace CategoryTheory.InternalAbelianSheafModule

section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max c v, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
variable {R S : Sheaf J AddCommGrpCat.{u}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
variable [HasDerivedCategory.{w} (scalarInternalModules J R)]
  [HasDerivedCategory.{w} (scalarInternalModules J S)]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J R))]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J S))]
attribute [local instance] sfbSheafTensor_monoidalPreadditive sfbSheafTensor_hasWeakSheafify

open SheafOfModules

-- Comparing the homotopy and complex factorization APIs needs additional elaboration.
omit [HasDerivedCategory (scalarInternalModules J R)]
  [HasDerivedCategory (scalarInternalModules J S)] in
private theorem sectionPair_exists :
    Nonempty (SheafOfModules.ScalarDerivedPair (sectionScalarMap J a)) := by
  classical
  let a := sectionScalarMap J a
  obtain ⟨E, hobj, hmap, hadd, _, _, F, ε, hF, _, hc⟩ :=
    derivedChangeOfRingsIndependentCoefficients a
  have := hadd
  obtain ⟨_, _, h⟩ := sheafRingDerivedCoefficientAdjunction a
  obtain ⟨am, hu, hd⟩ := h E hobj hmap
  obtain ⟨d, hn⟩ := hd F ε hF
  refine ⟨{ extension := E
            extension_obj := hobj
            extension_map := hmap
            extension_additive := hadd
            derived := F
            counit := ε
            isLeftDerived := hF
            computes := ?_
            ordinaryAdjunction := am
            ordinaryUnit := ?_
            adjunction := d
            normalization := ?_ }⟩
  · intro P hP
    have := hc P hP
    dsimp only [scalarPairComplexComparison]
    infer_instance
  · intro M V x
    have hh := hu M (changeOfRings a M) (𝟙 _) V x
    simp only [Category.comp_id] at hh
    have he := am.homEquiv_naturality_right (𝟙 (E.obj M)) (eqToHom (hobj M))
    simp only [Category.id_comp, am.homEquiv_id] at he
    rw [he] at hh
    exact hh
  · intro P hP hflat H g
    let q := HomotopyCategory.quotient (scalarModules J (sectionRingSheaf J R)) (.up ℤ)
    let q' := HomotopyCategory.quotient (scalarModules J (sectionRingSheaf J S)) (.up ℤ)
    have hh := ((hn P hP hflat).2.2 (q'.obj H) (q.map g)).1
    clear h hd hn hu hobj hmap hc hF
    have hfac : (scalarRestriction a).mapDerivedCategoryFactorsh.inv.app (q'.obj H) =
        (scalarRestriction a).mapDerivedCategoryFactors.inv.app H := by
      apply (Iso.inv_eq_inv
        ((scalarRestriction a).mapDerivedCategoryFactorsh.app (q'.obj H))
        ((scalarRestriction a).mapDerivedCategoryFactors.app H)).2
      change (scalarRestriction a).mapDerivedCategoryFactorsh.hom.app (q'.obj H) =
        (scalarRestriction a).mapDerivedCategoryFactors.hom.app H
      rw [Functor.mapDerivedCategoryFactorsh_hom_app]
      change (scalarRestriction a).mapDerivedCategory.map (𝟙 _) ≫
        (scalarRestriction a).mapDerivedCategoryFactors.hom.app H ≫ 𝟙 _ ≫
          DerivedCategory.Qh.map (𝟙 _) = _
      erw [(scalarRestriction a).mapDerivedCategory.map_id (DerivedCategory.Q.obj H),
        DerivedCategory.Qh.map_id ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((scalarRestriction a).mapHomologicalComplex (.up ℤ)).obj H))]
      simp only [Category.id_comp]
      exact Category.comp_id ((scalarRestriction a).mapDerivedCategoryFactors.hom.app H)
    have ht : ((am.mapHomotopyCategory (.up ℤ)).homEquiv (q.obj P) (q'.obj H)).symm
        (q.map g) = q'.map (((am.mapHomologicalComplex (.up ℤ)).homEquiv P H).symm g) := by
      rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
      erw [Adjunction.mapHomotopyCategory_counit_app_quotient]
      rw [Functor.mapHomotopyCategory_map, q'.map_comp]
    rw [hfac, ht] at hh
    change (d.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj H)).symm
        (DerivedCategory.Q.map g ≫ (scalarRestrictionComparison a).inv.app H) =
      ε.app (q.obj P) ≫ DerivedCategory.Q.map
        (scalarChainTranspose a E hadd am P H g) at hh
    have hcP : scalarPairComplexComparison E hadd F ε P = ε.app (q.obj P) := by
      dsimp only [scalarPairComplexComparison]
      change F.map (𝟙 _) ≫ ε.app (q.obj P) ≫ 𝟙 _ = ε.app (q.obj P)
      simp
    rw [hcP]
    exact hh

private noncomputable def scalarExtensionIso
    (s : SheafOfModules.ScalarDerivedPair (sectionScalarMap.{u, c, v} J a)) :
    Mod.extendScalars a ⋙ (sectionModuleEquivalence.{u, c, v} J S).functor ≅
      (sectionModuleEquivalence.{u, c, v} J R).functor ⋙ s.extension := by
  let α : (sectionModuleEquivalence.{u, c, v} J R).functor ⋙ s.extension ⟶
      Mod.extendScalars a ⋙ (sectionModuleEquivalence.{u, c, v} J S).functor :=
    ((mateEquiv (Mod.extendRestrictAdjunction a) s.ordinaryAdjunction).symm
    (TwoSquare.mk _ _ _ _ (scalarRestrictionIso.{u, c, v} (C := C) J a).hom))
  have : IsIso α := inverseMate_isIso
    (Mod.extendRestrictAdjunction a) s.ordinaryAdjunction
    (scalarRestrictionIso.{u, c, v} (C := C) J a)
  exact (asIso α).symm

omit [HasDerivedCategory (scalarInternalModules J R)]
  [HasDerivedCategory (scalarInternalModules J S)] in
private theorem scalarExtension_unit
    (s : SheafOfModules.ScalarDerivedPair (sectionScalarMap.{u, c, v} J a))
    (M : scalarInternalModules J R) :
    (sectionModuleEquivalence.{u, c, v} J R).functor.map
        ((Mod.extendRestrictAdjunction a).unit.app M) ≫
      (scalarRestrictionIso.{u, c, v} (C := C) J a).hom.app ((Mod.extendScalars a).obj M) =
    s.ordinaryAdjunction.unit.app ((sectionModuleEquivalence.{u, c, v} J R).functor.obj M) ≫
      (SheafOfModules.scalarRestriction (sectionScalarMap.{u, c, v} J a)).map
        ((scalarExtensionIso (C := C) J a s).inv.app M) :=
  unit_mateEquiv_symm (Mod.extendRestrictAdjunction a) s.ordinaryAdjunction
    (TwoSquare.mk _ _ _ _ (scalarRestrictionIso.{u, c, v} (C := C) J a).hom) M

omit [HasDerivedCategory (scalarInternalModules J R)]
  [HasDerivedCategory (scalarInternalModules J S)] in
private theorem scalarExtension_homEquiv
    (s : SheafOfModules.ScalarDerivedPair (sectionScalarMap.{u, c, v} J a))
    (M : scalarInternalModules J R) (N : scalarInternalModules J S)
    (f : (Mod.extendScalars a).obj M ⟶ N) :
    (sectionModuleEquivalence.{u, c, v} J R).functor.map
        ((Mod.extendRestrictAdjunction a).homEquiv M N f) ≫
      (scalarRestrictionIso.{u, c, v} (C := C) J a).hom.app N =
    s.ordinaryAdjunction.homEquiv _ _
      ((scalarExtensionIso (C := C) J a s).inv.app M ≫
        (sectionModuleEquivalence.{u, c, v} J S).functor.map f) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    Category.assoc]
  have h := (scalarRestrictionIso.{u, c, v} (C := C) J a).hom.naturality f
  change (sectionModuleEquivalence.{u, c, v} J R).functor.map ((Mod.comap a).map f) ≫ _ =
    _ ≫ (SheafOfModules.scalarRestriction (sectionScalarMap.{u, c, v} J a)).map
      ((sectionModuleEquivalence.{u, c, v} J S).functor.map f) at h
  rw [h]
  rw [← Category.assoc, scalarExtension_unit J a s M]
  simp only [Functor.map_comp, Category.assoc]

omit [HasDerivedCategory (scalarInternalModules J R)]
  [HasDerivedCategory (scalarInternalModules J S)] in
private theorem scalarExtension_unit_image
    (s : SheafOfModules.ScalarDerivedPair (sectionScalarMap.{u, c, v} J a))
    (M : scalarInternalModules J R) (U : Cᵒᵖ) (m : M.X.obj.obj U) :
    ((scalarExtensionIso (C := C) J a s).hom.app M).val.app U
        (((Mod.extendRestrictAdjunction a).unit.app M).hom.hom.app U m) =
      (s.ordinaryAdjunction.unit.app
        ((sectionModuleEquivalence.{u, c, v} J R).functor.obj M)).val.app U m := by
  have h := congrArg
    (fun f ↦ f ≫ (SheafOfModules.scalarRestriction (sectionScalarMap.{u, c, v} J a)).map
      ((scalarExtensionIso (C := C) J a s).hom.app M))
        (scalarExtension_unit J a s M)
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at h
  exact congrArg (fun f ↦ f.val.app U m) h

noncomputable local instance (U : Cᵒᵖ) (N : ModuleCat ((sectionRingSheaf J S).obj.obj U)) :
    SMul (S.obj.obj U) N :=
  inferInstanceAs (SMul ((sectionRingSheaf J S).obj.obj U) N)

omit [HasDerivedCategory (scalarInternalModules J R)]
  [HasDerivedCategory (scalarInternalModules J S)]
  [HasDerivedCategory (SheafOfModules.scalarModules J (sectionRingSheaf J R))]
  [HasDerivedCategory (SheafOfModules.scalarModules J (sectionRingSheaf J S))] in
private theorem internalScalarGenerator_eq_smul
    (M : scalarInternalModules J R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (m : M.X.obj.obj U) :
    internalScalarGenerator J a M U s m =
      s • (show ((sectionModuleEquivalence.{u, c, v} J S).functor.obj
        ((Mod.extendScalars a).obj M)).val.obj U from
          (((Mod.extendRestrictAdjunction a).unit.app M).hom.hom.app U m)) := by
  have h := congrArg (fun f ↦ f.hom.app U) (Mod.whiskerLeft_extendUnitHom_smul' a M)
  have hμ := congr_app (Functor.LaxMonoidal.μ_natural_right
    (sheafToPresheaf J AddCommGrpCat.{u}) S (Mod.extendUnitHom a M)) U
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f ≫ (Mod.act ((Mod.extendScalars a).obj M).X).hom.app U) hμ)
      (s ⊗ₜ[ℤ] m)
  change internalScalarGenerator J a M U s m = _
  change
    (((sheafToPresheaf J AddCommGrpCat.{u}).obj S ◁
      (sheafToPresheaf J AddCommGrpCat.{u}).map (Mod.extendUnitHom a M)).app U ≫
      ((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) S
        (Mod.extendScalarsObj a M).X).app U) ≫
      (Mod.act (Mod.extendScalarsObj a M).X).hom.app U) (s ⊗ₜ[ℤ] m) =
    (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) S M.X).app U) ≫
      (S ◁ Mod.extendUnitHom a M ≫ Mod.act (Mod.extendScalarsObj a M).X).hom.app U)
        (s ⊗ₜ[ℤ] m) at hh
  rw [h] at hh
  exact hh.symm

omit [HasDerivedCategory (scalarInternalModules J R)]
  [HasDerivedCategory (scalarInternalModules J S)] in
private theorem scalarExtension_generator
    (s : SheafOfModules.ScalarDerivedPair (sectionScalarMap J a))
    (M : scalarInternalModules J R) (U : Cᵒᵖ) (t : S.obj.obj U) (m : M.X.obj.obj U) :
    ((eqToHom (s.extension_obj ((sectionModuleEquivalence J R).functor.obj M))).val.app U)
        (((scalarExtensionIso J a s).hom.app M).val.app U
          (internalScalarGenerator J a M U t m)) =
      (toSheafify J (SheafOfModules.changeOfRingsPresheaf (sectionScalarMap J a)
        ((sectionModuleEquivalence J R).functor.obj M)).presheaf).app U
          (t ⊗ₜ[(sectionRingSheaf J R).obj.obj U, ((sectionScalarMap J a).hom.app U).hom] m) := by
  rw [internalScalarGenerator_eq_smul]
  rw [map_smul, scalarExtension_unit_image, map_smul, s.ordinaryUnit]
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J S)).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf (sectionScalarMap J a)
          ((sectionModuleEquivalence J R).functor.obj M))
  change t • (η.app U _ ) = η.app U _
  rw [← map_smul]
  congr 1
  simpa only [mul_one] using
    (ModuleCat.ExtendScalars.smul_tmul ((sectionScalarMap J a).hom.app U).hom
      (M := ((sectionModuleEquivalence J R).functor.obj M).val.obj U)
      (show (sectionRingSheaf J S).obj.obj U from t) 1 m)

/-- The complete normalized comparison, using the actual internal coequalizer extension,
actual sectionwise sheafification, and universal unbounded derived pairs. This proposition
asserts existence of the comparison data with all their normalization properties.
Source: Stacks 03EK, 0GMW, 06YS, 06YY, 07A6 and 09T5
(blueprint: lem-sfb-internal-section-scalar-adjunction). -/
def InternalSectionScalarAdjunction : Prop :=
  -- The recorded normalized sectionwise extension and its derived adjunction.
  ∃ sectionPair : (SheafOfModules.ScalarDerivedPair (sectionScalarMap J a)),
  -- Restriction commutes with reconstruction.
  ∃ restriction : (Mod.comap a ⋙ (sectionModuleEquivalence J R).functor ≅
    (sectionModuleEquivalence J S).functor ⋙
      SheafOfModules.scalarRestriction (sectionScalarMap J a)),
  -- The restriction identification is the identity on underlying sections.
  (∀ (N : scalarInternalModules J S) (U : Cᵒᵖ)
    (x : N.X.obj.obj U), (restriction.hom.app N).val.app U x = x) ∧
  -- Extension commutes with reconstruction.
  ∃ extension : (Mod.extendScalars a ⋙ (sectionModuleEquivalence J S).functor ≅
    (sectionModuleEquivalence J R).functor ⋙ sectionPair.extension),
  -- The comparison preserves every balanced generator, with no scalar twist.
  (∀ (M : scalarInternalModules J R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (m : M.X.obj.obj U),
    ((eqToHom
      (sectionPair.extension_obj ((sectionModuleEquivalence J R).functor.obj M))).val.app U)
        ((extension.hom.app M).val.app U (internalScalarGenerator J a M U s m)) =
      (toSheafify J (SheafOfModules.changeOfRingsPresheaf (sectionScalarMap J a)
        ((sectionModuleEquivalence J R).functor.obj M)).presheaf).app U
          (s ⊗ₜ[(sectionRingSheaf J R).obj.obj U, ((sectionScalarMap J a).hom.app U).hom] m)) ∧
  -- The specified ordinary Hom adjunctions agree, hence so do unit and counit.
  (∀ (M : scalarInternalModules J R) (N : scalarInternalModules J S)
    (f : (Mod.extendScalars a).obj M ⟶ N),
    (sectionModuleEquivalence J R).functor.map
        ((Mod.extendRestrictAdjunction a).homEquiv M N f) ≫ restriction.hom.app N =
      sectionPair.ordinaryAdjunction.homEquiv _ _
        (extension.inv.app M ≫ (sectionModuleEquivalence J S).functor.map f)) ∧
  -- The internal unbounded derived scalar extension.
  ∃ internalDerived : (DerivedCategory (scalarInternalModules J R) ⥤
    DerivedCategory (scalarInternalModules J S)),
  -- Its comparison on the actual complexes.
  ∃ internalCounit : (DerivedCategory.Q ⋙ internalDerived ⟶
    (Mod.extendScalars a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
  -- This is the universal left derived functor, not an arbitrary left adjoint.
  (internalDerived.IsLeftDerivedFunctor internalCounit
    (HomologicalComplex.quasiIso (scalarInternalModules J R) (.up ℤ))) ∧
  -- K-flat complexes compute the internal universal pair. K-flatness is transported
  -- by the recorded equivalence, as in internal_section_tensor_comparison.
  (∀ (P : CochainComplex (scalarInternalModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := sectionRingSheaf J R)
      (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P) →
        IsIso (internalCounit.app P)) ∧
  -- The specified internal derived extension/exact restriction adjunction.
  ∃ internalAdjunction : (internalDerived ⊣ (Mod.comap a).mapDerivedCategory),
  -- The internal derived unit is induced by the specified ordinary internal unit.
  -- This pins the derived adjunction independently of section reconstruction.
  (∀ (P : CochainComplex (scalarInternalModules J R) ℤ),
    internalAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (Mod.comap a).mapDerivedCategory.map (internalCounit.app P) ≫
        (Mod.comap a).mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars a).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((Mod.extendRestrictAdjunction a).mapHomologicalComplex (.up ℤ)).unit.app P)) ∧
  -- The termwise equivalences identify derived restrictions.
  ∃ derivedRestriction : ((Mod.comap a).mapDerivedCategory ⋙
      (sectionModuleEquivalence J R).functor.mapDerivedCategory ≅
    (sectionModuleEquivalence J S).functor.mapDerivedCategory ⋙
      SheafOfModules.scalarDerivedRestriction (sectionScalarMap J a)),
  -- Restriction comparison is precisely localization of the ordinary one.
  (derivedRestriction =
    Functor.mapDerivedCategoryCompIso (Mod.comap a)
      (sectionModuleEquivalence J R).functor ≪≫
    Functor.mapDerivedCategoryNatIso restriction ≪≫
    (Functor.mapDerivedCategoryCompIso (sectionModuleEquivalence J S).functor
      (SheafOfModules.scalarRestriction (sectionScalarMap J a))).symm) ∧
  -- The comparison of the universal derived extensions.
  ∃ derivedExtension : (internalDerived ⋙
      (sectionModuleEquivalence J S).functor.mapDerivedCategory ≅
    (sectionModuleEquivalence J R).functor.mapDerivedCategory ⋙ sectionPair.derived),
  -- On flat-term K-flat representatives, this is the localized termwise comparison.
  (∀ (P : CochainComplex (scalarInternalModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := sectionRingSheaf J R)
      (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := sectionRingSheaf J R)
      ((sectionModuleEquivalence J R).functor.obj (P.X n))) →
    (sectionModuleEquivalence J S).functor.mapDerivedCategory.map (internalCounit.app P) ≫
        (sectionModuleEquivalence J S).functor.mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars a).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex extension (.up ℤ)).hom.app P) =
      derivedExtension.hom.app (DerivedCategory.Q.obj P) ≫
        sectionPair.derived.map
          ((sectionModuleEquivalence J R).functor.mapDerivedCategoryFactors.hom.app P) ≫
        SheafOfModules.scalarPairComplexComparison sectionPair.extension
          sectionPair.extension_additive sectionPair.derived sectionPair.counit
          (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P)) ∧
  -- Agreement of the specified derived transposes includes derived units and counits.
  ∀ (M : DerivedCategory (scalarInternalModules J R))
      (N : DerivedCategory (scalarInternalModules J S)) (f : internalDerived.obj M ⟶ N),
      (sectionModuleEquivalence J R).functor.mapDerivedCategory.map
          (internalAdjunction.homEquiv M N f) ≫ derivedRestriction.hom.app N =
        sectionPair.adjunction.homEquiv _ _ (derivedExtension.inv.app M ≫
          (sectionModuleEquivalence J S).functor.mapDerivedCategory.map f)

/-- Scalar reconstruction preserves restriction, balanced extension and their specified
ordinary and unbounded derived adjunctions, with no flatness hypothesis on the ring map.
Source: Stacks 03EK, 0GMW, 06YS, 06YY, 07A6 and 09T5; blueprint
main-20261015, det-prop-scalar-six-pullback.proof.md, (1), first paragraph
(blueprint: lem-sfb-internal-section-scalar-adjunction).

Proof:
1. Internal restriction acts on each section by a(r)n. Reconstruction leaves the
underlying sheaf and every morphism fixed, giving the identity restriction comparison.
2. Apply lem-pe-internal-section-tensor-comparison to the restricted regular S-module
and M. Both extensions impose (s a(r)) tensor m = s tensor (rm). The comparison sends
s tensor m to itself and respects the S-action. Naturality is checked on these generators
using lem-pc-sites-sheaf-tensor-bilinear-universal.
3. The ordinary transpose sends f to (m ↦ f(1 tensor m)); its inverse sends g to
(s tensor m ↦ s g(m)). Balancing and the module axioms prove they are inverse.
The generator comparison preserves these formulas, including the unit and counit.
4. The exact section equivalences preserve quasi-isomorphisms, flat objects and K-flat
complexes by lem-pe-internal-section-tensor-comparison. Localizing them and the termwise
restriction identity gives the derived equivalences and exact restriction comparison.
5. Use lem-pc-kflat-resolution on the section side and pull the resolution back through
reconstruction. Transport the universal derived pair of lem-pur-derived-change-of-rings.
Its universal property is invariant under equivalences, and its comparison on a flat-term
K-flat resolution is localization of the generator-preserving termwise isomorphism.
6. The internal derived adjunction is normalized by the ordinary internal unit:
after internalCounit and the exact comap factorization, its unit on Q(P) is Q of
the ordinary chain unit. This is the defining unit compatibility of the derived
adjunction, transported along rightDerivedComapIsoMapDerivedCategory; it depends
only on the internal ordinary adjunction and universal derived comparison.
Apply lem-pur-sheaf-ring-derived-hom-comparison. The unit roof has second arrow
p ↦ 1 tensor p; the counit on a resolution q has map s tensor p ↦ s q(p).
The ordinary and representative comparisons preserve both maps and every resolution
arrow, so the normalized derived Hom transposes, units and counits agree. No step
requires flatness of a or preservation of K-flatness by restriction. -/
theorem internal_section_scalar_adjunction : InternalSectionScalarAdjunction J a := by
  obtain ⟨s⟩ := sectionPair_exists J a
  refine ⟨s, scalarRestrictionIso J a, ?_, scalarExtensionIso J a s, ?_, ?_, ?_⟩
  · intros
    rfl
  · exact scalarExtension_generator J a s
  · exact scalarExtension_homEquiv J a s
  · exact derived_section_scalar_transport J a (sectionScalarMap J a) s
      (scalarRestrictionIso J a) (scalarExtensionIso J a s) (scalarExtension_homEquiv J a s)

end

end CategoryTheory.InternalAbelianSheafModule
