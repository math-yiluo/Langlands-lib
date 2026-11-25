/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Compatible sectionwise bases of constant coefficient extensions

Source: Stacks 03EK and the finite-basis calculation in step 6 of
`lem-pur-compact-support-roos-cofinality`.
-/

@[expose] public section
set_option autoImplicit false
universe uC vC r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section BasisConstruction
private noncomputable def basisConst {C : Type uC} [Category.{vC} C]
    (A : CommRingCat.{r}) : ModuleCat.{r} A ⥤
      PresheafOfModules.{r} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) where
  obj M :=
    { obj := fun _ ↦ M
      map := fun _ ↦ ModuleCat.ofHom LinearMap.id
      map_id := fun _ ↦ by ext; rfl
      map_comp := fun _ _ ↦ by ext; rfl }
  map f := { app := fun _ ↦ f }

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{max uC vC r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  (A B : CommRingCat.{max uC vC r}) [Algebra A B]
private instance basisRingLocallyBijective :
    J.WEqualsLocallyBijective CommRingCat.{max uC vC r} := by
  let : EssentiallySmall.{max uC vC r} C := essentiallySmallSelf.{r} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{vC, max uC vC r,
    uC, (max uC vC r) + 1, max uC vC r, max uC vC r, max uC vC r} _
private noncomputable abbrev basisRing (A : CommRingCat.{max uC vC r}) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj ((constantSheaf J CommRingCat).obj A)
private noncomputable def basisRingUnit (A : CommRingCat.{max uC vC r}) :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ (basisRing.{uC, vC, r} J A).obj :=
  whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) (forget₂ CommRingCat RingCat)
private instance basisRingUnit_li :
    Presheaf.IsLocallyInjective J (basisRingUnit.{uC, vC, r} J A) := by
  let := basisRingLocallyBijective.{uC, vC, r} J
  exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (show CommRingCat.{max uC vC r} from A))) x y h⟩
private instance basisRingUnit_ls :
    Presheaf.IsLocallySurjective J (basisRingUnit.{uC, vC, r} J A) := by
  let := basisRingLocallyBijective.{uC, vC, r} J
  exact ⟨fun x ↦ Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (show CommRingCat.{max uC vC r} from A))) x⟩
private noncomputable def basisTarget : SheafOfModules.{max uC vC r} (basisRing.{uC, vC, r} J A) :=
  (SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map
    ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))).obj
      (SheafOfModules.unit (basisRing.{uC, vC, r} J B))
private noncomputable def basisConstToTarget :
    (basisConst A).obj (ModuleCat.of A B) ⟶
      (PresheafOfModules.restrictScalars (basisRingUnit.{uC, vC, r} J A)).obj
        (basisTarget.{uC, vC, r} J A B).val where
  app U := ModuleCat.ofHom (Y :=
    ((PresheafOfModules.restrictScalars (basisRingUnit.{uC, vC, r} J A)).obj
      (basisTarget.{uC, vC, r} J A B).val).obj U)
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
    (PresheafOfModules.sheafification (basisRingUnit.{uC, vC, r} J A)).obj
      ((basisConst A).obj (ModuleCat.of A B)) ⟶ basisTarget.{uC, vC, r} J A B :=
  (PresheafOfModules.sheafificationHomEquiv _).symm (basisConstToTarget.{uC, vC, r} J A B)

private instance basisLift_iso : IsIso (basisLift.{uC, vC, r} J A B) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)).mp
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff,
    ← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  let P := ((basisConst (C := C) A).obj (ModuleCat.of A B)).presheaf
  have h : toSheafify J P ≫
      ((SheafOfModules.toSheaf _).map (basisLift.{uC, vC, r} J A B)).hom =
        (PresheafOfModules.toPresheaf _).map
          (basisConstToTarget.{uC, vC, r} J A B) := by
    let E := PresheafOfModules.sheafificationHomEquiv
      (basisRingUnit.{uC, vC, r} J A)
      (P := (basisConst (C := C) A).obj (ModuleCat.of A B))
      (F := basisTarget.{uC, vC, r} J A B)
    have hh := E.apply_symm_apply (basisConstToTarget.{uC, vC, r} J A B)
    have hh' := congrArg (fun g ↦
      (PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of A))).map g) hh
    change toSheafify J P ≫ (PresheafOfModules.toPresheaf _).map
      (basisLift.{uC, vC, r} J A B).val = _
    rw [basisLift]
    exact hh'
  rw [← Presheaf.comp_isLocallyInjective_iff J (toSheafify J P),
    ← Presheaf.comp_isLocallySurjective_iff J (toSheafify J P)]
  change Presheaf.IsLocallyInjective J
    (toSheafify J P ≫ ((SheafOfModules.toSheaf _).map
      (basisLift.{uC, vC, r} J A B)).hom) ∧ _
  erw [h]
  let := basisRingLocallyBijective.{uC, vC, r} J
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)) x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)) x⟩

private noncomputable def basisTarget_self :
    basisTarget.{uC, vC, r} J A A ≅
      SheafOfModules.unit (basisRing.{uC, vC, r} J A) := by
  have h : ((sheafCompose J (forget₂ CommRingCat RingCat)).map
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A A)))) =
        𝟙 (basisRing.{uC, vC, r} J A) := by
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
    IsLimit (basisConstFan.{uC, vC, r} (C := C) A n) :=
  PresheafOfModules.evaluationJointlyReflectsLimits _ _
    (fun _ ↦ ModuleCat.productConeIsLimit (fun _ : Fin n ↦ ModuleCat.of A A))

private noncomputable def basisSheafIso (n : ℕ) (b : Module.Basis (Fin n) A B) :
    basisTarget.{uC, vC, r} J A B ≅
      ∏ᶜ (fun _ : Fin n ↦ SheafOfModules.unit (basisRing.{uC, vC, r} J A)) := by
  let F := PresheafOfModules.sheafification (basisRingUnit.{uC, vC, r} J A)
  let e : (basisConst (C := C) A).obj (ModuleCat.of A B) ≅
      ∏ᶜ (fun _ : Fin n ↦ (basisConst A).obj (ModuleCat.of A A)) :=
    (basisConst A).mapIso b.equivFun.toModuleIso ≪≫
      (limit.isoLimitCone ⟨_, basisConstFanLimit.{uC, vC, r} A n⟩).symm
  exact (asIso (basisLift.{uC, vC, r} J A B)).symm ≪≫ F.mapIso e ≪≫
    asIso (piComparison F (fun _ : Fin n ↦ (basisConst A).obj (ModuleCat.of A A))) ≪≫
    Pi.mapIso (fun _ ↦ asIso (basisLift.{uC, vC, r} J A A) ≪≫
      basisTarget_self.{uC, vC, r} J A)

private noncomputable def basisSectionIso (n : ℕ) (b : Module.Basis (Fin n) A B)
    (U : Cᵒᵖ) :
    (SheafOfModules.evaluation (basisRing.{uC, vC, r} J A) U).obj
        (basisTarget.{uC, vC, r} J A B) ≅
      ModuleCat.of ((basisRing.{uC, vC, r} J A).obj.obj U)
        (Fin n → (basisRing.{uC, vC, r} J A).obj.obj U) := by
  let E := SheafOfModules.evaluation (basisRing.{uC, vC, r} J A) U
  exact E.mapIso (basisSheafIso.{uC, vC, r} J A B n b) ≪≫
    asIso (piComparison E
      (fun _ : Fin n ↦ SheafOfModules.unit (basisRing.{uC, vC, r} J A))) ≪≫
      ModuleCat.piIsoPi _

private theorem basisSectionIso_coordinate (n : ℕ) (b : Module.Basis (Fin n) A B)
    (U : Cᵒᵖ) (s : (basisTarget.{uC, vC, r} J A B).val.obj U) (i : Fin n) :
    (basisSectionIso.{uC, vC, r} J A B n b U).hom s i =
      ((basisSheafIso.{uC, vC, r} J A B n b).hom ≫ Pi.π _ i).val.app U s := by
  change ((SheafOfModules.evaluation _ U).map
    (basisSheafIso.{uC, vC, r} J A B n b).hom ≫
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
      (basisSectionIso.{uC, vC, r} J A B n b U).toLinearEquiv
  refine ⟨b', ?_⟩
  intro U V f s i
  simp only [b', Module.Basis.equivFun_ofEquivFun]
  change (basisSectionIso.{uC, vC, r} J A B n b V).hom _ i =
    (((constantSheaf J CommRingCat).obj A).obj.map f)
      ((basisSectionIso.{uC, vC, r} J A B n b U).hom s i)
  rw [basisSectionIso_coordinate, basisSectionIso_coordinate]
  exact ConcreteCategory.congr_hom
    (((basisSheafIso.{uC, vC, r} J A B n b).hom ≫ Pi.π _ i).val.naturality f) s
end BasisConstruction

/-- A finite basis of a coefficient extension induces a basis on every object of
its constant ring sheaves, with coordinates commuting with restriction.

Source: Stacks 03EK, associated module sheaves, and the finite-basis argument of
step 6 of `lem-pur-compact-support-roos-cofinality`.
(blueprint: lem-pur-constant-finite-free-section-basis)

Proof: Choose a finite A-basis of B. Its coordinate maps give an A-linear
isomorphism B with A to a finite power. Regard these as maps of constant
abelian presheaves equipped with the constant A-action. Sheafify the maps and
their inverse identities. Associated sheafification preserves finite products,
and the forgetful functors from commutative rings commute with sheafification.
The resulting maps identify the underlying A-module sheaf of the constant B
with the corresponding finite power of the constant A. The action agrees with
the one induced by the constant algebra map: the scalar-linearity identity
holds on constant presheaves, and descends through sheafification by its
universal property (equivalently, check it on locally constant generators).
Taking sections therefore gives a linear equivalence on every object, which
transports the standard finite basis to b U. The coordinate maps are sheaf
morphisms, so they commute with restriction and satisfy the displayed equality.
This argument uses no assertion that all sections of a constant sheaf are
constant. On an empty covering object both section rings are zero, and the
same linear equivalence still holds. If A is the zero ring then B is zero;
use the empty basis and n=0. Rank zero and the empty site are covered as well. -/
theorem constantFiniteFree_sectionBasis
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{max uC vC r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (A B : CommRingCat.{max uC vC r}) [Algebra A B] [Module.Free A B]
    [Module.Finite A B] :
    let R := (constantSheaf J CommRingCat).obj A
    let S := (constantSheaf J CommRingCat).obj B
    let α := (constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))
    ∃ (n : ℕ) (b : ∀ U : Cᵒᵖ,
      @Module.Basis (Fin n) (R.obj.obj U) (S.obj.obj U) _ _
        (Module.compHom _ (α.hom.app U).hom)),
      ∀ (U V : Cᵒᵖ) (f : U ⟶ V) (s : S.obj.obj U) (i : Fin n),
        letI : Module (R.obj.obj U) (S.obj.obj U) :=
          Module.compHom _ (α.hom.app U).hom
        letI : Module (R.obj.obj V) (S.obj.obj V) :=
          Module.compHom _ (α.hom.app V).hom
        (b V).equivFun (S.obj.map f s) i = R.obj.map f ((b U).equivFun s i) := by
  classical
  let n := Fintype.card (Module.Free.ChooseBasisIndex A B)
  let b : Module.Basis (Fin n) A B :=
    (Module.Free.chooseBasis A B).reindex (Fintype.equivFin _)
  obtain ⟨b', hb'⟩ := basisConstruct.{uC, vC, r} J A B n b
  exact ⟨n, b', hb'⟩
end CategoryTheory
