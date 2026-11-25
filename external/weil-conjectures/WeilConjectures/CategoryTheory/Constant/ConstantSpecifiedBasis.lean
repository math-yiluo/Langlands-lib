/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Constant sheaves with a specified finite basis

Source: Stacks Project, Tags 03CY and 00WJ; the finite-basis argument in
`lem-pur-adic-basis-limit`, step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe uC vC r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section BasisConstruction
private noncomputable def basisConst {C : Type uC} [Category.{vC} C]
    (A : Type r) [CommRing A] : ModuleCat.{r} A ⥤
      PresheafOfModules.{r} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) where
  obj M :=
    { obj := fun _ ↦ M
      map := fun _ ↦ ModuleCat.ofHom LinearMap.id
      map_id := fun _ ↦ by ext; rfl
      map_comp := fun _ _ ↦ by ext; rfl }
  map f := { app := fun _ ↦ f }

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J RingCat.{max uC vC r}]
  [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  (A B : Type (max uC vC r)) [CommRing A] [CommRing B] [Algebra A B]
private noncomputable abbrev basisRing (A : Type (max uC vC r)) [CommRing A] :=
  (constantSheaf J RingCat.{max uC vC r}).obj (RingCat.of A)
private noncomputable def basisRingUnit (A : Type (max uC vC r)) [CommRing A] :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ (basisRing.{uC, vC, r} J A).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))
private instance basisRingLocallyBijective :
    J.WEqualsLocallyBijective RingCat.{max uC vC r} := by
  let : EssentiallySmall.{max uC vC r} C := essentiallySmallSelf.{r} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{vC, max uC vC r,
    uC, (max uC vC r) + 1, max uC vC r, max uC vC r, max uC vC r} _
private instance basisRingUnit_li :
    Presheaf.IsLocallyInjective J (basisRingUnit.{uC, vC, r} J A) := by
  let := basisRingLocallyBijective.{uC, vC, r} J
  dsimp only [basisRingUnit]
  infer_instance
private instance basisRingUnit_ls :
    Presheaf.IsLocallySurjective J (basisRingUnit.{uC, vC, r} J A) := by
  let := basisRingLocallyBijective.{uC, vC, r} J
  dsimp only [basisRingUnit]
  infer_instance
private noncomputable def basisTarget : SheafOfModules.{max uC vC r} (basisRing.{uC, vC, r} J A) :=
  (SheafOfModules.restrictScalars
    ((constantSheaf J RingCat.{max uC vC r}).map (RingCat.ofHom (algebraMap A B)))).obj
      (SheafOfModules.unit (basisRing.{uC, vC, r} J B))
private noncomputable def basisConstToTarget :
    (basisConst A).obj (ModuleCat.of A B) ⟶
      (PresheafOfModules.restrictScalars (basisRingUnit.{uC, vC, r} J A)).obj
        (basisTarget.{uC, vC, r} J A B).val where
  app U := ModuleCat.ofHom (Y :=
    ((PresheafOfModules.restrictScalars (basisRingUnit.{uC, vC, r} J A)).obj
      (basisTarget.{uC, vC, r} J A B).val).obj U)
    { toFun := (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        rw [Algebra.smul_def]
        change (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U
          (algebraMap A B a * b) = _
        rw [map_mul]
        congr 1
        exact congrArg (fun t ↦ t a) (NatTrans.congr_app
          (toSheafify_naturality J
            ((Functor.const Cᵒᵖ).map (RingCat.ofHom (algebraMap A B)))) U) }
  naturality {U V} f := by
    ext b
    exact ConcreteCategory.congr_hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).naturality f) b

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
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))) x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))) x⟩

private noncomputable def basisTarget_self :
    basisTarget.{uC, vC, r} J A A ≅
      SheafOfModules.unit (basisRing.{uC, vC, r} J A) := by
  have h : ((constantSheaf J RingCat.{max uC vC r}).map (RingCat.ofHom (algebraMap A A))) =
        𝟙 (basisRing.{uC, vC, r} J A) := by
    rw [show RingCat.ofHom (algebraMap A A) = 𝟙 (RingCat.of A) from rfl]
    exact (constantSheaf J RingCat.{max uC vC r}).map_id (RingCat.of A)
  refine
    { hom := { val :=
        { app := fun U ↦ ConcreteCategory.ofHom
            (C := ModuleCat ((basisRing.{uC, vC, r} J A).obj.obj U))
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun r x ↦ ?_ }
          naturality := fun _ ↦ by ext; rfl } }
      inv := { val :=
        { app := fun U ↦ ConcreteCategory.ofHom
            (C := ModuleCat ((basisRing.{uC, vC, r} J A).obj.obj U))
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun r x ↦ ?_ }
          naturality := fun _ ↦ by ext; rfl } }
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }
  · change ((constantSheaf J RingCat.{max uC vC r}).map
      (RingCat.ofHom (algebraMap A A))).hom.app U r *
      (show (basisRing.{uC, vC, r} J A).obj.obj U from x) =
        r * (show (basisRing.{uC, vC, r} J A).obj.obj U from x)
    rw [h]
    rfl
  · change r * (show (basisRing.{uC, vC, r} J A).obj.obj U from x) =
      ((constantSheaf J RingCat.{max uC vC r}).map
        (RingCat.ofHom (algebraMap A A))).hom.app U r *
          (show (basisRing.{uC, vC, r} J A).obj.obj U from x)
    rw [h]
    rfl

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

private theorem basisLift_constant (U : Cᵒᵖ) (x : B) :
    (basisLift.{uC, vC, r} J A B).val.app U
      ((toSheafify J ((basisConst (C := C) A).obj (ModuleCat.of A B)).presheaf).app U x) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U x := by
  have h := congrArg (fun g ↦
      (PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of A))).map g)
    ((PresheafOfModules.sheafificationHomEquiv
      (basisRingUnit.{uC, vC, r} J A)
      (P := (basisConst (C := C) A).obj (ModuleCat.of A B))
      (F := basisTarget.{uC, vC, r} J A B)).apply_symm_apply
      (basisConstToTarget.{uC, vC, r} J A B))
  rw [basisLift]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h U) x

private theorem basisMap_constant {M N : ModuleCat.{max uC vC r} A} (g : M ⟶ N)
    (U : Cᵒᵖ) (x : M) :
    ((PresheafOfModules.sheafification (basisRingUnit.{uC, vC, r} J A)).map
      ((basisConst A).map g)).val.app U
        ((toSheafify J ((basisConst (C := C) A).obj M).presheaf).app U x) =
      (toSheafify J ((basisConst (C := C) A).obj N).presheaf).app U (g x) := by
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J
      ((PresheafOfModules.toPresheaf _).map ((basisConst (C := C) A).map g))) U) x).symm

omit [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}] in
private theorem basisTarget_self_apply (U : Cᵒᵖ)
    (x : (basisTarget.{uC, vC, r} J A A).val.obj U) :
    (basisTarget_self.{uC, vC, r} J A).hom.val.app U x = x := by
  rfl

private theorem basisSheafIso_coordinate_constant (n : ℕ)
    (b : Module.Basis (Fin n) A B) (U : Cᵒᵖ) (x : B) (i : Fin n) :
    ((basisSheafIso.{uC, vC, r} J A B n b).hom ≫ Pi.π _ i).val.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U x) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U (b.equivFun x i) := by
  rw [← basisLift_constant.{uC, vC, r} J A B U x]
  change ((basisLift.{uC, vC, r} J A B ≫
    (basisSheafIso.{uC, vC, r} J A B n b).hom ≫ Pi.π _ i).val.app U) _ = _
  simp only [basisSheafIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc, Pi.mapIso_hom_π,
    piComparison_comp_π_assoc, Functor.mapIso_hom, asIso_hom]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, limit.isoLimitCone_inv_π]
  change (basisTarget_self.{uC, vC, r} J A).hom.val.app U
    ((basisLift.{uC, vC, r} J A A).val.app U
      (((PresheafOfModules.sheafification (basisRingUnit.{uC, vC, r} J A)).map
        ((basisConst A).map (ModuleCat.ofHom
          ((LinearMap.proj i).comp b.equivFun.toLinearMap)))).val.app U
            ((toSheafify J ((basisConst (C := C) A).obj (ModuleCat.of A B)).presheaf).app
              U x))) = _
  rw [basisTarget_self_apply, basisMap_constant, basisLift_constant]
  rfl

private def basisConstant (c : B) (U : Cᵒᵖ) :
    (basisRing.{uC, vC, r} J B).obj.obj U :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U c

private def basisColumn (c : B) :
    SheafOfModules.unit (basisRing.{uC, vC, r} J A) ⟶
      basisTarget.{uC, vC, r} J A B :=
  (basisTarget.{uC, vC, r} J A B).unitHomEquiv.symm
    ⟨fun U ↦ (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U c,
      fun {_ _} f ↦ ConcreteCategory.congr_hom
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).naturality f) c |>.symm⟩

omit [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}] in
private theorem basisColumn_apply (c : B) (U : Cᵒᵖ)
    (x : (basisRing.{uC, vC, r} J A).obj.obj U) :
    (basisColumn.{uC, vC, r} J A B c).val.app U x =
      ((constantSheaf J RingCat.{max uC vC r}).map (RingCat.ofHom (algebraMap A B))).hom.app U x *
        basisConstant.{uC, vC, r} J B c U := rfl

private def basisForward (n : ℕ) (b : Module.Basis (Fin n) A B) :
    (∏ᶜ (fun _ : Fin n ↦ SheafOfModules.unit (basisRing.{uC, vC, r} J A))) ⟶
      basisTarget.{uC, vC, r} J A B :=
  ∑ i : Fin n, Pi.π _ i ≫ basisColumn.{uC, vC, r} J A B (b i)

private theorem basisColumn_coordinate (n : ℕ) (b : Module.Basis (Fin n) A B)
    (i j : Fin n) :
    basisColumn.{uC, vC, r} J A B (b j) ≫
      (basisSheafIso.{uC, vC, r} J A B n b).hom ≫ Pi.π _ i =
        if j = i then 𝟙 _ else 0 := by
  apply (SheafOfModules.unit (basisRing.{uC, vC, r} J A)).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  change ((basisSheafIso.{uC, vC, r} J A B n b).hom ≫ Pi.π _ i).val.app U
    ((basisColumn.{uC, vC, r} J A B (b j)).val.app U
      (1 : (basisRing.{uC, vC, r} J A).obj.obj U)) = _
  rw [basisColumn_apply]
  simp only [map_one, one_mul]
  change ((basisSheafIso.{uC, vC, r} J A B n b).hom ≫ Pi.π _ i).val.app U
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U (b j)) = _
  rw [basisSheafIso_coordinate_constant, Module.Basis.equivFun_self]
  split
  · simp_all
  · simp_all
    rfl

private theorem basisForward_iso (n : ℕ) (b : Module.Basis (Fin n) A B) :
    IsIso (basisForward.{uC, vC, r} J A B n b) := by
  have h : basisForward.{uC, vC, r} J A B n b ≫
      (basisSheafIso.{uC, vC, r} J A B n b).hom = 𝟙 _ := by
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, Category.id_comp, basisForward,
      Preadditive.sum_comp]
    simp [basisColumn_coordinate, comp_ite]
  have heq : basisForward.{uC, vC, r} J A B n b =
      (basisSheafIso.{uC, vC, r} J A B n b).inv := by
    apply (cancel_mono (basisSheafIso.{uC, vC, r} J A B n b).hom).mp
    simpa using h
  rw [heq]
  infer_instance

/-- The specified finite basis induces the corresponding constant-ring-sheaf
isomorphism, with its actual basis-vector columns.

Source: Stacks Project, Tags 03CY and 00WJ, and the basis calculation in
`lem-pur-adic-basis-limit`, step 2 (blueprint: lem-pur-constant-specified-basis).

Proof: Regard the basis equivalence and its coordinate maps as morphisms of
constant presheaves of modules. Sheafify over the unit from the constant ring
presheaf to its associated ring sheaf. Module sheafification preserves finite
products. Its comparison with the constant ring sheaf is an isomorphism:
both units are locally bijective, and local bijectivity is equivalent to being
an isomorphism for sheaves. Under the resulting coordinate isomorphism, the
constant section of the j-th basis vector has i-th coordinate delta(i,j).
Therefore the finite sum of the coordinate projections followed by
multiplication by these constant sections is the inverse isomorphism. Its
sectionwise formula is the displayed finite sum. This argument includes the
empty basis and objects admitting empty covering sieves. -/
theorem constantSheaf_specifiedBasis (n : ℕ) (b : Module.Basis (Fin n) A B)
    (f : A →+* B) (hf : f = algebraMap A B) :
    ∃ β : (∏ᶜ (fun _ : Fin n ↦ SheafOfModules.unit
          ((constantSheaf J RingCat.{max uC vC r}).obj (RingCat.of A)))) ≅
        (SheafOfModules.restrictScalars
          ((constantSheaf J RingCat.{max uC vC r}).map
            (RingCat.ofHom f))).obj
              (SheafOfModules.unit
                ((constantSheaf J RingCat.{max uC vC r}).obj (RingCat.of B))),
      ∀ (U : Cᵒᵖ)
        (y : (∏ᶜ (fun _ : Fin n ↦ SheafOfModules.unit
          ((constantSheaf J RingCat.{max uC vC r}).obj (RingCat.of A)))).val.obj U),
        β.hom.val.app U y = ∑ i : Fin n,
          ((constantSheaf J RingCat.{max uC vC r}).map
            (RingCat.ofHom f)).hom.app U
              ((Pi.π (fun _ : Fin n ↦ SheafOfModules.unit
                ((constantSheaf J RingCat.{max uC vC r}).obj (RingCat.of A))) i).val.app U y) *
          (show ((constantSheaf J RingCat.{max uC vC r}).obj (RingCat.of B)).obj.obj U from
            (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U (b i)) := by
  subst f
  let := basisForward_iso.{uC, vC, r} J A B n b
  refine ⟨asIso (basisForward.{uC, vC, r} J A B n b), ?_⟩
  intro U y
  change ((SheafOfModules.evaluation.{max uC vC r} (basisRing.{uC, vC, r} J A) U).map
    (∑ i : Fin n, Pi.π
      (fun _ : Fin n ↦ SheafOfModules.unit (basisRing.{uC, vC, r} J A)) i ≫
        basisColumn.{uC, vC, r} J A B (b i))) y = _
  let : (SheafOfModules.evaluation.{max uC vC r}
      (basisRing.{uC, vC, r} J A) U).Additive :=
    inferInstanceAs (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ U).Additive
  rw [Functor.map_sum]
  change (∑ i : Fin n, ((SheafOfModules.evaluation.{max uC vC r}
    (basisRing.{uC, vC, r} J A) U).map
      (Pi.π (fun _ : Fin n ↦ SheafOfModules.unit (basisRing.{uC, vC, r} J A)) i ≫
        basisColumn.{uC, vC, r} J A B (b i)))).hom y = _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact basisColumn_apply.{uC, vC, r} J A B (b i) U _

end BasisConstruction
end CategoryTheory
