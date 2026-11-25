/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Opposites
import WeilConjectures.CategoryTheory.DerivedSectionScalarTransport
public import WeilConjectures.CategoryTheory.InternalSectionScalarAdjunction

/-! # Scalar adjunctions under section reconstruction

Source: Stacks Project, Modules on Sites, Tags 03EK and 0GMW; Cohomology on Sites,
Tags 06YS, 06YY and 07A6; Derived Categories, Tag 09T5; blueprint main-20261015,
det-prop-scalar-six-pullback.proof.md, (1), first paragraph
(blueprint: lem-sfb-internal-section-scalar-adjunction).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


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

variable {R S : Sheaf J AddCommGrpCat.{u}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]


variable [HasDerivedCategory.{w} (scalarInternalModules J R)]
  [HasDerivedCategory.{w} (scalarInternalModules J S)]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J R))]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J S))]

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



end CategoryTheory.InternalAbelianSheafModule
