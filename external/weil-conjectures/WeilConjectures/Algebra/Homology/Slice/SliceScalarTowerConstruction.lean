/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearSliceScalarGeneratorsBasic
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators

/-! # Scalar-extension towers

Source: Stacks Project, Modules on Sites, Tags 03EK and 03CZ.
(blueprint: lem-sf-slice-scalar-tower-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r
open CategoryTheory Opposite
attribute [local implicit_reducible] CategoryTheory.sheafCompose

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

open scoped ChangeOfRings

variable (O : Sheaf J CommRingCat.{max c v r})
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r})
  (α : (Functor.const ℕᵒᵖ).obj O ⟶ B)
  (D : ∀ n, SystemScalarModel.{c, v, max c v r} (α.app (op n)))

private theorem model_pure {R S : Sheaf J CommRingCat.{max c v r}} {φ : R ⟶ S}
    (A : SystemScalarModel.{c, v, max c v r} φ)
    (P : ringedSiteModules.{max c v r} (derivedChangeRingIndependentCoefficients.{max c v r, c, v}
      J R))
    (W : Cᵒᵖ) (b : S.obj.obj W) (x : P.val.obj W) :
    (eqToHom (A.model.obj_eq P)).val.app W
        (systemModelTmul.{c, v, max c v r} A.model P W b x) = sliceScalarPure.{c, v, r} φ P W x b
          := by
  simp only [systemModelTmul, map_smul, ← ModuleCat.comp_apply,
    ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
    eqToHom_trans, eqToHom_refl, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]
  change b • ((PresheafOfModules.sheafificationAdjunction.{max c v r, v, max c v r, c}
    (𝟙 (derivedChangeRingIndependentCoefficients.{max c v r, c, v} J S).obj)).unit.app
    (changeOfRingsPresheaf.{v, c, max c v r} φ P)).app W ((1 : S.obj.obj W) ⊗ₜ[R.obj.obj W,
      (φ.hom.app W).hom] x) = _
  rw [← map_smul]
  change ((PresheafOfModules.sheafificationAdjunction.{max c v r, v, max c v r, c}
    (𝟙 (derivedChangeRingIndependentCoefficients.{max c v r, c, v} J S).obj)).unit.app
    (changeOfRingsPresheaf.{v, c, max c v r} φ P)).app W ((b * 1) ⊗ₜ[R.obj.obj W, (φ.hom.app
      W).hom] x) = _
  rw [mul_one]
  rfl

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem algebra_comp {m n : ℕ} (h : m ≤ n) :
    α.app (op m) = α.app (op n) ≫ B.map (homOfLE h).op := by
  have hn := α.naturality (homOfLE h).op
  change 𝟙 O ≫ α.app (op m) = α.app (op n) ≫ B.map (homOfLE h).op at hn
  simpa only [Category.id_comp] using hn

private def scalarTransition
    (H : ringedSiteModules.{max c v r} (derivedChangeRingIndependentCoefficients.{max c v r, c, v}
      J O))
    {m n : ℕ} (h : m ≤ n) :
    (D n).model.E.obj H ⟶ (systemRestriction.{c, v, max c v r} B h).obj ((D m).model.E.obj H) :=
  ((D n).ordinaryAdj.homEquiv _ _).symm
    ((D m).ordinaryAdj.unit.app H ≫
      (systemScalarRestrictionComposition.{c, v, max c v r} (α.app (op n)) (B.map (homOfLE h).op)
        (α.app (op m)) (algebra_comp.{c, v, r} O B α h)).inv.app ((D m).model.E.obj H))

private theorem scalarTransition_pure
    (H : ringedSiteModules.{max c v r} (derivedChangeRingIndependentCoefficients.{max c v r, c, v}
      J O))
    {m n : ℕ} (h : m ≤ n) (W : Cᵒᵖ)
    (b : (B.obj (op n)).obj.obj W) (x : H.val.obj W) :
    (scalarTransition.{c, v, r} O B α D H h).val.app W
        (systemModelTmul.{c, v, max c v r} (D n).model H W b x) =
      systemModelTmul.{c, v, max c v r} (D m).model H W ((B.map (homOfLE h).op).hom.app W b) x := by
  rw [systemScalarModel_transpose_tmul.{c, v, max c v r}]
  unfold scalarTransition
  rw [Equiv.apply_symm_apply]
  have hu := (D m).unit_normalized H W x
  dsimp only [systemModelTmul] at hu
  rw [one_smul] at hu
  change (fun y : ((D m).model.E.obj H).val.obj W ↦
    (B.map (homOfLE h).op).hom.app W b • y)
      (((D m).ordinaryAdj.unit.app H).val.app W x) = _
  exact congrArg (fun y : ((D m).model.E.obj H).val.obj W ↦
    (B.map (homOfLE h).op).hom.app W b • y) hu

private theorem scalarTransition_identity
    (H : ringedSiteModules.{max c v r} (derivedChangeRingIndependentCoefficients.{max c v r, c, v}
      J O))
    (n : ℕ) (W : Cᵒᵖ) (x : ((D n).model.E.obj H).val.obj W) :
    (scalarTransition.{c, v, r} O B α D H (Nat.le_refl n)).val.app W x = x := by
  let η := systemScalarRestrictionUnit.{c, v, max c v r} (B.map (homOfLE (Nat.le_refl n)).op)
    (B.map_id (op n))
  have he : scalarTransition.{c, v, r} O B α D H (Nat.le_refl n) =
      η.inv.app ((D n).model.E.obj H) := by
    apply systemScalarModel_hom_ext.{c, v, max c v r} (D n)
    intro V y
    change (scalarTransition.{c, v, r} O B α D H (Nat.le_refl n)).val.app V _ =
      systemModelTmul.{c, v, max c v r} (D n).model H V 1 y
    simpa only [map_one] using
      scalarTransition_pure.{c, v, r} O B α D H (Nat.le_refl n) V 1 y
  exact congrArg (fun f ↦ f.val.app W x) he

private theorem scalarTransition_compose
    (H : ringedSiteModules.{max c v r} (derivedChangeRingIndependentCoefficients.{max c v r, c, v}
      J O))
    {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) (W : Cᵒᵖ)
    (x : ((D n).model.E.obj H).val.obj W) :
    (scalarTransition.{c, v, r} O B α D H (h.trans k)).val.app W x =
      (scalarTransition.{c, v, r} O B α D H h).val.app W
        ((scalarTransition.{c, v, r} O B α D H k).val.app W x) := by
  have hc : B.map (homOfLE (h.trans k)).op =
      B.map (homOfLE k).op ≫ B.map (homOfLE h).op := by
    rw [← B.map_comp]
    rfl
  let η := systemScalarRestrictionComposition.{c, v, max c v r} _ _ _ hc
  have he : scalarTransition.{c, v, r} O B α D H (h.trans k) =
      scalarTransition.{c, v, r} O B α D H k ≫
        (systemRestriction.{c, v, max c v r} B k).map (scalarTransition.{c, v, r} O B α D H h) ≫
        η.hom.app ((D l).model.E.obj H) := by
    apply systemScalarModel_hom_ext.{c, v, max c v r} (D n)
    intro V y
    change (scalarTransition.{c, v, r} O B α D H (h.trans k)).val.app V _ =
      (scalarTransition.{c, v, r} O B α D H h).val.app V
        ((scalarTransition.{c, v, r} O B α D H k).val.app V
          (systemModelTmul.{c, v, max c v r} (D n).model H V 1 y))
    rw [scalarTransition_pure.{c, v, r}, scalarTransition_pure.{c, v, r}]
    simp only [map_one]
    rw [scalarTransition_pure.{c, v, r}]
    simp only [map_one]
  exact congrArg (fun f ↦ f.val.app W x) he

private theorem scalarTransition_naturality
    {H H' : ringedSiteModules.{max c v r} (derivedChangeRingIndependentCoefficients.{max c v r, c,
      v} J O)}
    (f : H ⟶ H') {m n : ℕ} (h : m ≤ n) :
    (D n).model.E.map f ≫ scalarTransition.{c, v, r} O B α D H' h =
      scalarTransition.{c, v, r} O B α D H h ≫
        (systemRestriction.{c, v, max c v r} B h).map ((D m).model.E.map f) := by
  apply systemScalarModel_hom_ext.{c, v, max c v r} (D n)
  intro W x
  change (scalarTransition.{c, v, r} O B α D H' h).val.app W
    (((D n).model.E.map f).val.app W _) =
      ((D m).model.E.map f).val.app W ((scalarTransition.{c, v, r} O B α D H h).val.app W _)
  rw [systemScalarModel_map_tmul.{c, v, max c v r}, scalarTransition_pure.{c, v, r},
    scalarTransition_pure.{c, v, r},
    systemScalarModel_map_tmul.{c, v, max c v r}]
  rfl

private def scalarTowerObject
    (H : ringedSiteModules.{max c v r} (derivedChangeRingIndependentCoefficients.{max c v r, c, v}
      J O)) :
    StrictRingSystem.{c, v, max c v r} B where
  level n := (D n).model.E.obj H
  transition := scalarTransition.{c, v, r} O B α D H
  identity := scalarTransition_identity.{c, v, r} O B α D H
  compose := scalarTransition_compose.{c, v, r} O B α D H

private def scalarTowerFunctor :
    ringedSiteModules.{max c v r} (derivedChangeRingIndependentCoefficients.{max c v r, c, v} J O) ⥤
      StrictRingSystem.{c, v, max c v r} B where
  obj := scalarTowerObject.{c, v, r} O B α D
  map f :=
    { app := fun n ↦ (D n).model.E.map f
      comm := scalarTransition_naturality.{c, v, r} O B α D f }
  map_id H := strictRingSystem_hom_ext B _ _ (fun n ↦ (D n).model.E.map_id H)
  map_comp f g := strictRingSystem_hom_ext B _ _ (fun n ↦ (D n).model.E.map_comp f g)

private theorem scalarTowerFunctor_additive : (scalarTowerFunctor.{c, v, r} O B α D).Additive := by
  constructor
  intro H H' f g
  apply strictRingSystem_hom_ext B
  intro n
  change (D n).model.E.map (f + g) = (systemEvaluation B n).map
    ((scalarTowerFunctor.{c, v, r} O B α D).map f +
      (scalarTowerFunctor.{c, v, r} O B α D).map g)
  rw [Functor.map_add, Functor.map_add]
  rfl

private theorem model_pure_inv {R S : Sheaf J CommRingCat.{max c v r}} {φ : R ⟶ S}
    (A : SystemScalarModel.{c, v, max c v r} φ)
    (P : ringedSiteModules.{max c v r} (derivedChangeRingIndependentCoefficients.{max c v r, c, v}
      J R))
    (W : Cᵒᵖ) (b : S.obj.obj W) (x : P.val.obj W) :
    (eqToHom (A.model.obj_eq P).symm).val.app W (sliceScalarPure.{c, v, r} φ P W x b) =
      systemModelTmul.{c, v, max c v r} A.model P W b x := by
  have h := congrArg ((eqToHom (A.model.obj_eq P).symm).val.app W)
    (model_pure.{c, v, r} A P W b x)
  simpa only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] using h.symm

/-- Scalar extension along an algebra tower gives its prescribed additive strict tower.
Source: Stacks Project, Modules on Sites, Tags 03EK and 03CZ
(blueprint: lem-sf-slice-scalar-tower-construction).

Proof: At level n use sheafification of the presheaf B_n tensor_O H, and on a
module map use sheafification of id tensor f. For m ≤ n, the presheaf map sends
b tensor x to q(b) tensor x; it is semilinear since q is an O-algebra map, and
therefore induces a map into the scalar restriction of the level-m sheafification.
The sheafification universal property extends this map uniquely. The identity,
composition and naturality equations hold on pure tensors by functoriality of q,
and hence hold after sheafification. Tensor maps and sheafification are additive.
The scalar-extension adjunction unit is x ↦ 1 tensor x before sheafification.
The transition equation for these units follows from q(1)=1. These constructions
supply every field, with the model's prescribed object and map identifications. -/
theorem exists_sliceScalarTowerPresentation
    (O : Sheaf J CommRingCat.{max c v r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r})
    (α : (Functor.const ℕᵒᵖ).obj O ⟶ B) :
    Nonempty (SliceScalarTowerPresentation.{c, v, r} O B α) := by
  classical
  have hd : ∀ n, Nonempty (SystemScalarModel.{c, v, max c v r} (α.app (op n))) :=
    fun n ↦ nonempty_systemScalarModel.{c, v, max c v r} (α.app (op n))
  let D : ∀ n, SystemScalarModel.{c, v, max c v r} (α.app (op n)) := fun n ↦ (hd n).some
  refine ⟨{
    F := scalarTowerFunctor.{c, v, r} O B α D
    obj_eq := fun H n ↦ (D n).model.obj_eq H
    map_eq := fun f n ↦ (D n).model.map_eq f
    transition_pure := ?_
    unit := fun H n ↦ (D n).ordinaryAdj.unit.app H
    unit_pure := ?_
    unit_transition := ?_
    additive := scalarTowerFunctor_additive.{c, v, r} O B α D }⟩
  · intro H m n h W x b
    change (eqToHom ((D m).model.obj_eq H)).val.app W
      ((scalarTransition.{c, v, r} O B α D H h).val.app W
        ((eqToHom ((D n).model.obj_eq H).symm).val.app W _)) = _
    rw [model_pure_inv.{c, v, r}, scalarTransition_pure.{c, v, r}, model_pure.{c, v, r}]
  · intro H n W x
    change (eqToHom ((D n).model.obj_eq H)).val.app W
      (((D n).ordinaryAdj.unit.app H).val.app W x) = _
    rw [(D n).unit_normalized]
    exact model_pure.{c, v, r} (D n) H W 1 x
  · intro H m n h W x
    change (scalarTransition.{c, v, r} O B α D H h).val.app W
      (((D n).ordinaryAdj.unit.app H).val.app W x) = _
    rw [(D n).unit_normalized, scalarTransition_pure.{c, v, r}, map_one]
    exact ((D m).unit_normalized H W x).symm

end SheafOfModules
