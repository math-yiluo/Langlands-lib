/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair

/-! # Ordinary constraints for signed tensor powers -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.SignedLineDerivedBaseChange
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal

local instance {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R : Sheaf K CommRingCat.{w}}
    (M : SheafOfModules.{w} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
    (V : Dᵒᵖ) :
    SMul (((PresheafOfModules.restrictOver R.obj V.unop).obj
      (unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)).val).obj
        (op (Over.mk (𝟙 V.unop)))) (M.val.obj V) :=
  (M.val.obj V).isModule.toSMul

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  (A : Sheaf J CommRingCat.{max u v w})

private theorem tensor_three_ext (M L N H : KFlatFixedTensor.Modules A)
    (f g : (siteSheafTensorRight N).obj ((siteSheafTensorRight L).obj M) ⟶ H)
    (h : ∀ V x y z, f.val.app V
      (siteSheafTensorTmul _ N V (siteSheafTensorTmul M L V x y) z) =
      g.val.app V (siteSheafTensorTmul _ N V (siteSheafTensorTmul M L V x y) z)) :
    f = g := by
  apply scalarTensor_hom_ext
  intro V xy z
  let η := scalarSheafificationUnit (siteTensorPresheaf M.val L.val)
  apply H.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) xy)
  intro W i hi
  obtain ⟨t, ht⟩ := hi
  change η.app (op W) t = ((siteSheafTensorRight L).obj M).val.map i.op xy at ht
  change H.val.map i.op (f.val.app V _) = H.val.map i.op (g.val.app V _)
  rw [← PresheafOfModules.naturality_apply f.val,
    ← PresheafOfModules.naturality_apply g.val, scalarTensorTmul_naturality, ← ht]
  clear ht
  induction t using TensorProduct.inductionOn with
  | add t t' ih ih' => simp only [map_add, scalarTensorTmul_add_first, ih, ih']
  | tmul x y => exact h (op W) x y (N.val.map i.op z)

private def ordinary_unit : siteSheafTensorRight (unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) ≅ 𝟭 _ :=
  NatIso.ofComponents (scalarTensorRightUnitor A) (by
    intro M N f
    apply scalarTensor_hom_ext
    intro V x r
    change (scalarTensorRightUnitor A N).hom.val.app V
      (((siteSheafTensorRight _).map f).val.app V
        (siteSheafTensorTmul M _ V x r)) =
      f.val.app V ((scalarTensorRightUnitor A M).hom.val.app V
        (siteSheafTensorTmul M _ V x r))
    rw [scalarTensor_first_tmul, scalarTensorRightUnitor_tmul,
      scalarTensorRightUnitor_tmul, map_smul])

private def ordinary_product (L N : KFlatFixedTensor.Modules A) :
    siteSheafTensorRight L ⋙ siteSheafTensorRight N ≅
      siteSheafTensorRight ((siteSheafTensorRight N).obj L) :=
  NatIso.ofComponents (fun M ↦ scalarTensorAssociatorIso A M L N) (by
    intro M M' f
    apply tensor_three_ext.{u, v, w} A M L N _
    intro V x y z
    change (scalarTensorAssociatorIso A M' L N).hom.val.app V
      (((siteSheafTensorRight N).map ((siteSheafTensorRight L).map f)).val.app V
        (siteSheafTensorTmul _ N V (siteSheafTensorTmul M L V x y) z)) =
      ((siteSheafTensorRight _).map f).val.app V
        ((scalarTensorAssociatorIso A M L N).hom.val.app V
          (siteSheafTensorTmul _ N V (siteSheafTensorTmul M L V x y) z))
    rw [scalarTensor_first_tmul, scalarTensor_first_tmul,
      scalarTensorAssociatorIso_tmul, scalarTensorAssociatorIso_tmul,
      scalarTensor_first_tmul])

private def eval_presheaf (L : KFlatFixedTensor.Modules A) :
    siteTensorPresheaf (homObj L (unit _)).val L.val ⟶ (unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)).val where
  app V := ModuleCat.ofHom
    (X := (siteTensorPresheaf (homObj L (unit _)).val L.val).obj V)
    (Y := (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)).val.obj V)
    (TensorProduct.lift (LineEvaluation.evalLinear.{u, v, max u v w} A L V))
  naturality {V W} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro φ y
    exact LineEvaluation.eval_restrict.{u, v, max u v w} A L f φ y

private def eval_pair (L : KFlatFixedTensor.Modules A) :
    (siteSheafTensorRight L).obj (homObj L (unit _)) ⟶ unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) :=
  ((PresheafOfModules.sheafificationAdjunction (R :=
    (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).homEquiv _ _).symm
      (eval_presheaf.{u, v, w} A L)

private theorem eval_pair_pure (L : KFlatFixedTensor.Modules A)
    (V : Cᵒᵖ) (φ : (homObj L (unit _)).val.obj V) (y : L.val.obj V) :
    (eval_pair.{u, v, w} A L).val.app V (siteSheafTensorTmul _ L V φ y) =
      φ.app (op (Over.mk (𝟙 V.unop))) y := by
  let adj := PresheafOfModules.sheafificationAdjunction (R :=
    (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)
  have h := (adj.homEquiv
    (siteTensorPresheaf (homObj L (unit _)).val L.val)
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))).apply_symm_apply
      (eval_presheaf.{u, v, w} A L)
  exact congrArg (fun f ↦ f.app V (φ ⊗ₜ[A.obj.obj V] y)) h

private def ordinary_eval_map (L M : KFlatFixedTensor.Modules A) :
    (siteSheafTensorRight L).obj
      ((siteSheafTensorRight (homObj L (unit _))).obj M) ⟶ M :=
  (scalarTensorAssociatorIso A M (homObj L (unit _)) L).hom ≫
    siteSheafTensorSecondMap M (eval_pair.{u, v, w} A L) ≫
    (scalarTensorRightUnitor A M).hom

private theorem ordinary_eval_pure (L M : KFlatFixedTensor.Modules A)
    (V : Cᵒᵖ) (x : M.val.obj V) (φ : (homObj L (unit _)).val.obj V)
    (y : L.val.obj V) :
    (ordinary_eval_map.{u, v, w} A L M).val.app V
      (siteSheafTensorTmul _ L V (siteSheafTensorTmul M _ V x φ) y) =
      (φ.app (op (Over.mk (𝟙 V.unop))) y) • x := by
  change (scalarTensorRightUnitor A M).hom.val.app V
    ((siteSheafTensorSecondMap M _).val.app V
      ((scalarTensorAssociatorIso A M (homObj L (unit _)) L).hom.val.app V _)) = _
  rw [scalarTensorAssociatorIso_tmul, scalarTensor_second_tmul,
    scalarTensorRightUnitor_tmul, eval_pair_pure]

private def ordinary_evaluation (L : KFlatFixedTensor.Modules A) :
    siteSheafTensorRight (homObj L (unit _)) ⋙ siteSheafTensorRight L ⟶ 𝟭 _ where
  app M := ordinary_eval_map.{u, v, w} A L M
  naturality {M N} f := by
    apply tensor_three_ext.{u, v, w} A M (homObj L (unit _)) L _
    intro V x φ y
    change (ordinary_eval_map.{u, v, w} A L N).val.app V
      (((siteSheafTensorRight L).map ((siteSheafTensorRight _).map f)).val.app V
        (siteSheafTensorTmul _ L V (siteSheafTensorTmul M _ V x φ) y)) =
      f.val.app V ((ordinary_eval_map.{u, v, w} A L M).val.app V
        (siteSheafTensorTmul _ L V (siteSheafTensorTmul M _ V x φ) y))
    rw [scalarTensor_first_tmul, scalarTensor_first_tmul,
      ordinary_eval_pure, ordinary_eval_pure, map_smul]

/-- The unit, reassociation and evaluation of signed powers have their sectionwise formulas.
Source: Stacks Project, Modules on Sites, Tags 03EK, 03EL and 0FNY.
(blueprint: lem-pur-signed-line-ordinary-constraints)
Proof: sheafify the sectionwise tensor unitor and associator. Their naturality follows
by generation by pure tensors; for a triple tensor, first pass to a cover on which the
inner section comes from its presheaf tensor. Evaluation is reassociation, the tensor
of a functional with its argument, the usual internal-Hom evaluation, and the unitor.
The sheafification-unit formula gives contraction by the value of that functional.
Naturality follows from linearity, again checked on local pure tensors. -/
theorem signed_line_ordinary_constraints (P : KFlatFixedTensor.Modules A) :
  ∃ ordinaryUnit : siteSheafTensorRight (signedLinePower.{u, v, w} P 0) ≅ 𝟭 _,
  ∃ ordinaryProduct : ∀ n : ℕ,
    siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⋙
        siteSheafTensorRight (signedLinePower.{u, v, w} P 1) ≅
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 2))),
  ∃ ordinaryEvaluation : ∀ n : ℕ,
    siteSheafTensorRight (signedLinePower.{u, v, w} P (.negSucc n)) ⋙
      siteSheafTensorRight (signedLinePower.{u, v, w} P (.ofNat (n + 1))) ⟶ 𝟭 _,
    (∀ (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (r : A.obj.obj V),
      (ordinaryUnit.hom.app N).val.app V
        (siteSheafTensorTmul N (signedLinePower.{u, v, w} P 0) V x r) =
          @SMul.smul (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.obj V)
            (N.val.obj V) inferInstance r x) ∧
    (∀ (n : ℕ) (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (y : (scalarTensorPower A P (n + 1)).val.obj V)
      (q : P.val.obj V),
      ((ordinaryProduct n).hom.app N).val.app V
        (siteSheafTensorTmul _ P V
          (siteSheafTensorTmul N (scalarTensorPower A P (n + 1)) V x y) q) =
        siteSheafTensorTmul N (scalarTensorPower A P (n + 2)) V x
          (siteSheafTensorTmul (scalarTensorPower A P (n + 1)) P V y q)) ∧
    (∀ (n : ℕ) (N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
      (x : N.val.obj V) (φ : (signedLinePower.{u, v, w} P (.negSucc n)).val.obj V)
      (y : (scalarTensorPower A P (n + 1)).val.obj V),
      ((ordinaryEvaluation n).app N).val.app V
        (siteSheafTensorTmul _ (scalarTensorPower A P (n + 1)) V
          (siteSheafTensorTmul N (signedLinePower.{u, v, w} P (.negSucc n)) V x φ) y) =
        @SMul.smul (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.obj V)
          (N.val.obj V) inferInstance (φ.app (op (Over.mk (𝟙 V.unop))) y) x) := by
  refine ⟨ordinary_unit.{u, v, w} A,
    (fun n ↦ ordinary_product.{u, v, w} A (scalarTensorPower A P (n + 1)) P),
    (fun n ↦ ordinary_evaluation.{u, v, w} A (scalarTensorPower A P (n + 1))), ?_, ?_, ?_⟩
  · intro M V x r
    exact scalarTensorRightUnitor_tmul A M V x r
  · intro n M V x y q
    exact scalarTensorAssociatorIso_tmul A M (scalarTensorPower A P (n + 1)) P V x y q
  · intro n M V x φ y
    exact ordinary_eval_pure.{u, v, w} A (scalarTensorPower A P (n + 1)) M V x φ y

end SheafOfModules.SignedLineDerivedBaseChange
