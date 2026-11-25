/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Restricted scalar-first K-flat tensor identifications

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 06YT, and
sites-modules.tex, Tags 03EK and 03CY.
(blueprint: lem-pe-restricted-kflat-tensor-identification)

The scalar-last complex is specified by its underlying B-linear tensor complex and
its S-linear swap from the existing scalar-first extension. The pure-tensor equation
fixes the swap, including its inverse, and hence fixes the S-action on the last factor.
No existence choice of an unspecified object or map is used in a definition.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v r wB wA wS wT
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- Ordinary scalar restriction on the given site.
Source: Stacks 03DA (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorScalars {A S : Sheaf J CommRingCat.{r}} (v : A ⟶ S) :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map v)

/-- The coefficient sheaf as a module over the source ring.
Source: Stacks 03EK (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorCoefficient
    {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S) :=
  (restrictedTensorScalars φ).obj (unit (derivedChangeRingIndependentCoefficients J S))

namespace RestrictedTensorProof

variable [HasWeakSheafify J AddCommGrpCat.{r}]

attribute [local irreducible] monoidalCategory cochainModulesMonoidal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option hygiene false in
local notation "𝓡" R => derivedChangeRingIndependentCoefficients J R
set_option hygiene false in
local notation "𝓻" a => (sheafCompose J (forget₂ CommRingCat RingCat)).map a

private noncomputable def restrictSheafifyHom
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj M) ⟶
    (restrictScalars α).obj ((PresheafOfModules.sheafification (𝟙 S.obj)).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.app M))

private theorem restrictSheafifyHom_toSheaf
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (toSheaf R).map (restrictSheafifyHom α M) =
      𝟙 ((PresheafOfModules.toPresheaf S.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj M) := by
  rw [restrictSheafifyHom, PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  change (PresheafOfModules.toPresheaf S.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.app M) =
    CategoryTheory.toSheafify J M.presheaf
  exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _

attribute [local irreducible] restrictSheafifyHom

private theorem restrictSheafifyHom_isIso
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    IsIso (restrictSheafifyHom α M) := by
  have : IsIso ((toSheaf R).map (restrictSheafifyHom α M)) := by
    rw [restrictSheafifyHom_toSheaf]
    exact IsIso.id _
  exact isIso_of_reflects_iso _ (toSheaf R)

attribute [local instance] restrictSheafifyHom_isIso

private noncomputable def restrictSheafifyIso
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj M) ≅
    (restrictScalars α).obj ((PresheafOfModules.sheafification (𝟙 S.obj)).obj M) :=
  asIso (restrictSheafifyHom α M)

attribute [local irreducible] restrictSheafifyIso

@[simp] private theorem restrictSheafifyIso_hom_toSheaf
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (toSheaf R).map (restrictSheafifyIso α M).hom =
      𝟙 ((PresheafOfModules.toPresheaf S.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj M) := by
  unfold restrictSheafifyIso
  exact restrictSheafifyHom_toSheaf α M

@[simp] private theorem restrictSheafifyIso_inv_toSheaf
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (toSheaf R).map (restrictSheafifyIso α M).inv =
      𝟙 ((PresheafOfModules.toPresheaf S.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj M) := by
  have he : (toSheaf R).mapIso (restrictSheafifyIso α M) =
      Iso.refl ((PresheafOfModules.toPresheaf S.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj M) := by
    apply Iso.ext
    exact restrictSheafifyIso_hom_toSheaf α M
  exact congrArg Iso.inv he

private noncomputable def swapApp {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf φ M)).obj U ≅
    (siteTensorPresheaf M.val (restrictedTensorCoefficient φ).val).obj U := by
  let e : (((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf φ M)).obj U) ≃ₗ[B.obj.obj U]
      TensorProduct (B.obj.obj U) ((restrictedTensorCoefficient φ).val.obj U) (M.val.obj U) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro b x
        induction x using TensorProduct.inductionOn with
        | tmul s m => rfl
        | add x y hx hy => simpa only [smul_add] using congrArg₂ (· + ·) hx hy }
  exact (e.trans (TensorProduct.comm _ _ _)).toModuleIso

private theorem swapApp_tmul {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (swapApp φ M U).hom (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m) =
      m ⊗ₜ[B.obj.obj U] (show (restrictedTensorCoefficient φ).val.obj U from s) := rfl

attribute [local irreducible] swapApp

private noncomputable def swapPresheafIso {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).obj (changeOfRingsPresheaf φ M) ≅
      siteTensorPresheaf M.val (restrictedTensorCoefficient φ).val :=
  PresheafOfModules.isoMk (swapApp φ M) (by
    intro U V i
    ext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      change (swapApp φ M V).hom (changeOfRingsMap φ M i
        (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m)) = _
      erw [Classical.choose_spec (exists_changeOfRingsMap φ M i) s m]
      rw [swapApp_tmul]
      change _ = (siteTensorPresheaf M.val (restrictedTensorCoefficient φ).val).map i
        ((swapApp φ M U).hom (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m))
      rw [swapApp_tmul]
      rfl)

private theorem swapPresheafIso_tmul {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (swapPresheafIso φ M).hom.app U (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m) =
      m ⊗ₜ[B.obj.obj U] (show (restrictedTensorCoefficient φ).val.obj U from s) :=
  swapApp_tmul φ M U s m

attribute [local irreducible] swapPresheafIso

private noncomputable def swapSheafIso {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) :
    (restrictedTensorScalars φ).obj (changeOfRings φ M) ≅
      (siteSheafTensorRight (restrictedTensorCoefficient φ)).obj M :=
  (restrictSheafifyIso (𝓻 φ) (changeOfRingsPresheaf φ M)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (𝓡 B).obj)).mapIso (swapPresheafIso φ M)

private noncomputable def changeMap {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    {M N : SheafOfModules.{r} (𝓡 B)} (a : M ⟶ N) :
    changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ N where
  app U := (ModuleCat.extendScalars (φ.hom.app U).hom).map (a.val.app U)
  naturality := changeOfRingsHom_naturality φ M a

private theorem swapSheafIso_toSheaf {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) :
    (toSheaf (𝓡 B)).map (swapSheafIso φ M).hom =
      (presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf (𝓡 B).obj).map (swapPresheafIso φ M).hom) := by
  change (toSheaf (𝓡 B)).map
      ((restrictSheafifyIso (𝓻 φ) (changeOfRingsPresheaf φ M)).inv ≫
        (PresheafOfModules.sheafification (𝟙 (𝓡 B).obj)).map
          (swapPresheafIso φ M).hom) = _
  rw [Functor.map_comp, restrictSheafifyIso_inv_toSheaf]
  erw [Category.id_comp]
  rfl

attribute [local irreducible] swapSheafIso

private theorem swapSheafIso_naturality {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    {M N : SheafOfModules.{r} (𝓡 B)} (a : M ⟶ N) :
    (restrictedTensorScalars φ).map (changeOfRingsHom φ M a) ≫
      (swapSheafIso φ N).hom =
    (swapSheafIso φ M).hom ≫ (siteSheafTensorRight (restrictedTensorCoefficient φ)).map a := by
  have hp : (PresheafOfModules.restrictScalars (𝓻 φ).hom).map (changeMap φ a) ≫
      (swapPresheafIso φ N).hom =
    (swapPresheafIso φ M).hom ≫ siteTensorHom a.val (restrictedTensorCoefficient φ).val := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      change (swapPresheafIso φ N).hom.app U
          (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] a.val.app U m) =
        (siteTensorHom a.val (restrictedTensorCoefficient φ).val).app U
          ((swapPresheafIso φ M).hom.app U
            (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m))
      rw [swapPresheafIso_tmul, swapPresheafIso_tmul]
      rfl
  apply (toSheaf (𝓡 B)).map_injective
  simp only [Functor.map_comp, swapSheafIso_toSheaf]
  change (presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf (𝓡 B).obj).map
        ((PresheafOfModules.restrictScalars (𝓻 φ).hom).map (changeMap φ a))) ≫ _ =
    _ ≫ (presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf (𝓡 B).obj).map
        (siteTensorHom a.val (restrictedTensorCoefficient φ).val))
  simp only [← Functor.map_comp]
  rw [hp]

private theorem swapSheafIso_tmul {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (swapSheafIso φ M).hom.val.app U
      ((CategoryTheory.toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m)) =
      siteSheafTensorTmul M (restrictedTensorCoefficient φ) U m s := by
  have hn := CategoryTheory.toSheafify_naturality J
    ((PresheafOfModules.toPresheaf (𝓡 B).obj).map (swapPresheafIso φ M).hom)
  change ((toSheaf (𝓡 B)).map (swapSheafIso φ M).hom).hom.app U _ = _
  rw [swapSheafIso_toSheaf]
  have ht := (CategoryTheory.congr_fun (NatTrans.congr_app hn U)
    (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m)).symm
  change _ = (CategoryTheory.toSheafify J
    (siteTensorPresheaf M.val (restrictedTensorCoefficient φ).val).presheaf).app U
      ((swapPresheafIso φ M).hom.app U
        (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m)) at ht
  rw [swapPresheafIso_tmul] at ht
  exact ht



end RestrictedTensorProof

variable {B A S T : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wA} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J A))]
  [HasDerivedCategory.{wS} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S))]

open RestrictedTensorProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ordinarySwapIso {φ : B ⟶ S}
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} φ) :
    D.E ⋙ restrictedTensorScalars φ ≅ siteSheafTensorRight (restrictedTensorCoefficient φ) :=
  NatIso.ofComponents (fun M ↦
    (restrictedTensorScalars φ).mapIso (eqToIso (D.obj_eq M)) ≪≫ swapSheafIso φ M) (by
      intro M N a
      dsimp
      rw [D.map_eq]
      simp only [Functor.map_comp, Category.assoc, eqToHom_map,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [swapSheafIso_naturality φ a])

variable [HasDerivedCategory.{wT} (ringedSiteModules.{r}
  (derivedChangeRingIndependentCoefficients J T))]

end SheafOfModules
