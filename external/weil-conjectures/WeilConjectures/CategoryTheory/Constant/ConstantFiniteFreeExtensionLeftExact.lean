/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.CategoryTheory.RingedCoefficientCounit.RingedCoefficientCounitPresentations
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import all WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreePowerIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Left exactness of finite-free constant scalar extension

Source: Stacks 03CZ and 03EK; finite-basis argument in
`lem-pur-topos-finite-free-compact-constituents`, proof Step 1.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v r
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedCoefficientCounit

open CategoryTheory.Functor Opposite

namespace CategoryTheory.ConstantFiniteFreeIndependent

-- The section-basis construction from ConstantFiniteFreeSectionBasis, with
-- the existing EssentiallySmall hypothesis instead of a maximum of universes.
section BasisConstruction
private noncomputable def basisConst {C : Type u} [Category.{v} C]
    (A : CommRingCat.{r}) : ModuleCat.{r} A ⥤
      PresheafOfModules.{r} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) where
  obj M :=
    { obj := fun _ ↦ M
      map := fun _ ↦ ModuleCat.ofHom LinearMap.id
      map_id := fun _ ↦ by ext; rfl
      map_comp := fun _ _ ↦ by ext; rfl }
  map f := { app := fun _ ↦ f }

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (A B : CommRingCat.{r}) [Algebra A B]
private instance basisRingLocallyBijective :
    J.WEqualsLocallyBijective CommRingCat.{r} := by
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, r,
    u, (r) + 1, r, r, r} _
private noncomputable abbrev basisRing (A : CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj ((constantSheaf J CommRingCat).obj A)
private noncomputable def basisRingUnit (A : CommRingCat.{r}) :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ (basisRing.{u, v, r} J A).obj :=
  whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) (forget₂ CommRingCat RingCat)
private instance basisRingUnit_li :
    Presheaf.IsLocallyInjective J (basisRingUnit.{u, v, r} J A) := by
  let := basisRingLocallyBijective.{u, v, r} J
  exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (show CommRingCat.{r} from A))) x y h⟩
private instance basisRingUnit_ls :
    Presheaf.IsLocallySurjective J (basisRingUnit.{u, v, r} J A) := by
  let := basisRingLocallyBijective.{u, v, r} J
  exact ⟨fun x ↦ Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (show CommRingCat.{r} from A))) x⟩
private noncomputable def basisTarget : SheafOfModules.{r} (basisRing.{u, v, r} J A) :=
  (SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map
    ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))).obj
      (SheafOfModules.unit (basisRing.{u, v, r} J B))
private noncomputable def basisConstToTarget :
    (basisConst A).obj (ModuleCat.of A B) ⟶
      (PresheafOfModules.restrictScalars (basisRingUnit.{u, v, r} J A)).obj
        (basisTarget.{u, v, r} J A B).val where
  app U := ModuleCat.ofHom (Y :=
    ((PresheafOfModules.restrictScalars (basisRingUnit.{u, v, r} J A)).obj
      (basisTarget.{u, v, r} J A B).val).obj U)
    { toFun := (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        rw [Algebra.smul_def]
        change (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U
          (algebraMap A B a * b) = _
        rw [map_mul]
        congr 1
        exact congrArg (fun t ↦ t a) (NatTrans.congr_app
          (toSheafify_naturality J
            ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom (algebraMap A B)))) U) }
  naturality {U V} f := by
    ext b
    exact ConcreteCategory.congr_hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).naturality f) b

@[irreducible]
private noncomputable def basisLift :
    (PresheafOfModules.sheafification (basisRingUnit.{u, v, r} J A)).obj
      ((basisConst A).obj (ModuleCat.of A B)) ⟶ basisTarget.{u, v, r} J A B :=
  (PresheafOfModules.sheafificationHomEquiv _).symm (basisConstToTarget.{u, v, r} J A B)

private instance basisLift_iso : IsIso (basisLift.{u, v, r} J A B) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)).mp
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff,
    ← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  let P := ((basisConst (C := C) A).obj (ModuleCat.of A B)).presheaf
  have h : toSheafify J P ≫
      ((SheafOfModules.toSheaf _).map (basisLift.{u, v, r} J A B)).hom =
        (PresheafOfModules.toPresheaf _).map
          (basisConstToTarget.{u, v, r} J A B) := by
    let E := PresheafOfModules.sheafificationHomEquiv
      (basisRingUnit.{u, v, r} J A)
      (P := (basisConst (C := C) A).obj (ModuleCat.of A B))
      (F := basisTarget.{u, v, r} J A B)
    have hh := E.apply_symm_apply (basisConstToTarget.{u, v, r} J A B)
    have hh' := congrArg (fun g ↦
      (PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of A))).map g) hh
    change toSheafify J P ≫ (PresheafOfModules.toPresheaf _).map
      (basisLift.{u, v, r} J A B).val = _
    rw [basisLift]
    exact hh'
  rw [← Presheaf.comp_isLocallyInjective_iff J (toSheafify J P),
    ← Presheaf.comp_isLocallySurjective_iff J (toSheafify J P)]
  change Presheaf.IsLocallyInjective J
    (toSheafify J P ≫ ((SheafOfModules.toSheaf _).map
      (basisLift.{u, v, r} J A B)).hom) ∧ _
  erw [h]
  let := basisRingLocallyBijective.{u, v, r} J
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)) x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)) x⟩

private noncomputable def basisTarget_self :
    basisTarget.{u, v, r} J A A ≅
      SheafOfModules.unit (basisRing.{u, v, r} J A) := by
  have h : ((sheafCompose J (forget₂ CommRingCat RingCat)).map
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A A)))) =
        𝟙 (basisRing.{u, v, r} J A) := by
    rw [show CommRingCat.ofHom (algebraMap A A) = 𝟙 A from rfl]
    change ((constantSheaf J CommRingCat) ⋙
      sheafCompose J (forget₂ CommRingCat RingCat)).map (𝟙 A) = _
    exact ((constantSheaf J CommRingCat) ⋙
      sheafCompose J (forget₂ CommRingCat RingCat)).map_id A
  dsimp only [basisTarget]
  rw [h]
  exact Iso.refl _

private noncomputable def basisConstFan (n : ℕ) :
    Fan (fun _ : Fin n ↦ (basisConst (C := C) A).obj (ModuleCat.of A A)) :=
  Fan.mk ((basisConst A).obj (ModuleCat.of A (Fin n → A)))
    (fun i ↦ (basisConst A).map (ModuleCat.ofHom (LinearMap.proj i)))

private noncomputable def basisConstFanLimit (n : ℕ) :
    IsLimit (basisConstFan.{u, v, r} (C := C) A n) :=
  PresheafOfModules.evaluationJointlyReflectsLimits _ _
    (fun _ ↦ ModuleCat.productConeIsLimit (fun _ : Fin n ↦ ModuleCat.of A A))

private noncomputable def basisSheafIso (n : ℕ) (b : Module.Basis (Fin n) A B) :
    basisTarget.{u, v, r} J A B ≅
      ∏ᶜ (fun _ : Fin n ↦ SheafOfModules.unit (basisRing.{u, v, r} J A)) := by
  let F := PresheafOfModules.sheafification (basisRingUnit.{u, v, r} J A)
  let e : (basisConst (C := C) A).obj (ModuleCat.of A B) ≅
      ∏ᶜ (fun _ : Fin n ↦ (basisConst A).obj (ModuleCat.of A A)) :=
    (basisConst A).mapIso b.equivFun.toModuleIso ≪≫
      (limit.isoLimitCone ⟨_, basisConstFanLimit.{u, v, r} A n⟩).symm
  exact (asIso (basisLift.{u, v, r} J A B)).symm ≪≫ F.mapIso e ≪≫
    asIso (piComparison F (fun _ : Fin n ↦ (basisConst A).obj (ModuleCat.of A A))) ≪≫
    Pi.mapIso (fun _ ↦ asIso (basisLift.{u, v, r} J A A) ≪≫
      basisTarget_self.{u, v, r} J A)

private noncomputable def basisSectionIso (n : ℕ) (b : Module.Basis (Fin n) A B)
    (U : Cᵒᵖ) :
    (SheafOfModules.evaluation (basisRing.{u, v, r} J A) U).obj
        (basisTarget.{u, v, r} J A B) ≅
      ModuleCat.of ((basisRing.{u, v, r} J A).obj.obj U)
        (Fin n → (basisRing.{u, v, r} J A).obj.obj U) := by
  let E := SheafOfModules.evaluation (basisRing.{u, v, r} J A) U
  exact E.mapIso (basisSheafIso.{u, v, r} J A B n b) ≪≫
    asIso (piComparison E
      (fun _ : Fin n ↦ SheafOfModules.unit (basisRing.{u, v, r} J A))) ≪≫
      ModuleCat.piIsoPi _

private theorem basisSectionIso_coordinate (n : ℕ) (b : Module.Basis (Fin n) A B)
    (U : Cᵒᵖ) (s : (basisTarget.{u, v, r} J A B).val.obj U) (i : Fin n) :
    (basisSectionIso.{u, v, r} J A B n b U).hom s i =
      ((basisSheafIso.{u, v, r} J A B n b).hom ≫ Pi.π _ i).val.app U s := by
  change ((SheafOfModules.evaluation _ U).map
    (basisSheafIso.{u, v, r} J A B n b).hom ≫
      piComparison (SheafOfModules.evaluation _ U) _ ≫
      (ModuleCat.piIsoPi _).hom ≫ ModuleCat.ofHom (LinearMap.proj i)) s = _
  rw [ModuleCat.piIsoPi_hom_ker_subtype,
    piComparison_comp_π]
  rfl

private theorem basisConstruct (n : ℕ) (b : Module.Basis (Fin n) A B) :
    let R := (constantSheaf J CommRingCat).obj A
    let S := (constantSheaf J CommRingCat).obj B
    let α := (constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))
    ∃ (b' : ∀ U : Cᵒᵖ,
      @Module.Basis (Fin n) (R.obj.obj U) (S.obj.obj U) _ _
        (Module.compHom _ (α.hom.app U).hom)),
      ∀ (U V : Cᵒᵖ) (f : U ⟶ V) (s : S.obj.obj U) (i : Fin n),
        letI : Module (R.obj.obj U) (S.obj.obj U) :=
          Module.compHom _ (α.hom.app U).hom
        letI : Module (R.obj.obj V) (S.obj.obj V) :=
          Module.compHom _ (α.hom.app V).hom
        (b' V).equivFun (S.obj.map f s) i = R.obj.map f ((b' U).equivFun s i) := by
  let b' (U : Cᵒᵖ) :
      @Module.Basis (Fin n) (((constantSheaf J CommRingCat).obj A).obj.obj U)
        (((constantSheaf J CommRingCat).obj B).obj.obj U) _ _
        (Module.compHom _ (((constantSheaf J CommRingCat).map
          (CommRingCat.ofHom (algebraMap A B))).hom.app U).hom) := by
    letI : Module (((constantSheaf J CommRingCat).obj A).obj.obj U)
        (((constantSheaf J CommRingCat).obj B).obj.obj U) :=
      Module.compHom _ (((constantSheaf J CommRingCat).map
        (CommRingCat.ofHom (algebraMap A B))).hom.app U).hom
    exact Module.Basis.ofEquivFun
      (basisSectionIso.{u, v, r} J A B n b U).toLinearEquiv
  refine ⟨b', ?_⟩
  intro U V f s i
  simp only [b', Module.Basis.equivFun_ofEquivFun]
  change (basisSectionIso.{u, v, r} J A B n b V).hom _ i =
    (((constantSheaf J CommRingCat).obj A).obj.map f)
      ((basisSectionIso.{u, v, r} J A B n b U).hom s i)
  rw [basisSectionIso_coordinate, basisSectionIso_coordinate]
  exact ConcreteCategory.congr_hom
    (((basisSheafIso.{u, v, r} J A B n b).hom ≫ Pi.π _ i).val.naturality f) s
end BasisConstruction

end CategoryTheory.ConstantFiniteFreeIndependent

/-- Ordinary sheafified extension of finite-free constant scalars is left exact.

Source: Stacks Project, Modules on Sites, Tags 03CZ and 03EK; the finite-basis
argument in proof Step 1 of lem-pur-topos-finite-free-compact-constituents.
(blueprint: lem-pur-constant-finite-free-extension-left-exact).

Proof: choose a finite A-basis of B and its dual coordinates. On constant ring
presheaves the basis expansion and the Kronecker identities are inverse formulas.
Sheafifying gives a finite basis of the constant B-sheaf as a module over the
constant A-sheaf. This does not assert that its sections are constant. For any
module sheaf M, tensoring the basis and its dual coordinates identifies the
underlying abelian sheaf of E(M) with the corresponding finite power of the
underlying abelian sheaf of M. Check the inverse identities on pure tensors and
then use the universal property of module sheafification. These identifications
are natural by the prescribed map equation. Finite powers preserve finite limits,
as does the forgetful functor from module sheaves to abelian sheaves. That
forgetful functor reflects finite limits, so E preserves them. All formulas use
finite sums and also apply to the empty basis and to the zero coefficient ring.
The assumed sheafifications suffice with independent site and coefficient universes. -/
theorem CategoryTheory.constantFiniteFree_extensionLeftExact
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (A B : CommRingCat.{r}) [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (E : modules (constantRing J A) ⥤ modules (constantRing J B))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings
      ((constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom (algebraMap A B))) M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom
        ((constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom (algebraMap A B)))
          M f ≫ eqToHom (h N).symm) : PreservesFiniteLimits E := by
  classical
  let : HasSheafify J CommRingCat.{r} :=
    hasSheafifyEssentiallySmallSite.{v, r, u, r + 1, r} J CommRingCat.{r}
  let n := Fintype.card (Module.Free.ChooseBasisIndex A B)
  let b : Module.Basis (Fin n) A B :=
    (Module.Free.chooseBasis A B).reindex (Fintype.equivFin _)
  obtain ⟨b', hb⟩ := ConstantFiniteFreeIndependent.basisConstruct J A B n b
  let R := constantRing J A
  let S := constantRing J B
  let α : R ⟶ S :=
    (constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom (algebraMap A B))
  let F := SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj
  let G := SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj
  let e : E ⋙ F ≅ G ⋙ Functor.const (Discrete (Fin n)) ⋙ lim :=
    NatIso.ofComponents
      (fun M ↦ F.mapIso (eqToIso (h M)) ≪≫ sheafifiedTensorIso α n b' hb M ≪≫
        Pi.isoLimit ((Functor.const (Discrete (Fin n))).obj M.val.presheaf)) (by
      intro M N f
      dsimp only [Iso.trans_hom]
      simp only [Category.assoc]
      change F.map (E.map f) ≫ F.map (eqToIso (h N)).hom ≫ _ =
        F.map (eqToIso (h M)).hom ≫ _
      rw [← Category.assoc, ← F.map_comp]
      have he : E.map f ≫ (eqToIso (h N)).hom =
          (eqToIso (h M)).hom ≫ SheafOfModules.changeOfRingsHom α M f := by
        dsimp only [α]
        rw [hm]
        simp
      rw [he, F.map_comp, Category.assoc]
      have hn := sheafifiedTensorIso_naturality α n b' hb f
      change F.map (SheafOfModules.changeOfRingsHom α M f) ≫
        (sheafifiedTensorIso α n b' hb N).hom = _ at hn
      rw [reassoc_of% hn]
      congr 1
      congr 1
      apply limit.hom_ext
      rintro ⟨a⟩
      change Limits.Pi.map (f := fun _ : Fin n ↦ M.val.presheaf)
          (g := fun _ : Fin n ↦ N.val.presheaf)
          (fun _ ↦ (PresheafOfModules.toPresheaf _).map f.val) ≫
        (Pi.isoLimit ((Functor.const (Discrete (Fin n))).obj N.val.presheaf)).hom ≫
          limit.π ((Functor.const (Discrete (Fin n))).obj N.val.presheaf) ⟨a⟩ =
        (Pi.isoLimit ((Functor.const (Discrete (Fin n))).obj M.val.presheaf)).hom ≫
          limMap ((Functor.const (Discrete (Fin n))).map
            ((PresheafOfModules.toPresheaf _).map f.val)) ≫
          limit.π ((Functor.const (Discrete (Fin n))).obj N.val.presheaf) ⟨a⟩
      rw [Pi.isoLimit_hom_π]
      conv_rhs => erw [limMap_π]
      rw [Pi.isoLimit_hom_π_assoc]
      exact Pi.map_π _ _)
  have : PreservesFiniteLimits G := inferInstance
  have : PreservesFiniteLimits (E ⋙ F) := preservesFiniteLimits_of_natIso e.symm
  have : ReflectsFiniteLimits F := ⟨fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms⟩
  exact preservesFiniteLimits_of_reflects_of_preserves E F
