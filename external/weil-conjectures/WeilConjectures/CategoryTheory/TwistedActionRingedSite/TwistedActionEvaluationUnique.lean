/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TensorRestriction.TwistedActionTensorRestrictionSupplement

/-! # Uniqueness of the ordinary sheaf-Hom evaluation pairing

Source: Stacks Project, Tags 03EK and 03EO, on sheaf tensor and internal Hom.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.TwistedActionRingedSite

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}}

attribute [local irreducible] SheafOfModules.monoidalCategory

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private abbrev tensorAdj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ring S).obj)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem evaluation_pure (M N : Modules S) (X : Dᵒᵖ)
    (x : M.val.obj X) (φ : (SheafOfModules.homObj (R := S) M N).val.obj X) :
    (evaluationMap M N).val.app X
      (pureTensor M (SheafOfModules.homObj (R := S) M N) X x φ) =
        (φ.app (op (Over.mk (𝟙 X.unop)))).hom x := by
  let adj := tensorAdj (S := S)
  let t := PresheafOfModules.tensorHomUncurry
    (𝟙 (SheafOfModules.homObj (R := S) M N).val)
  have he : (SheafOfModules.tensorObjIsoSheafification M
      (SheafOfModules.homObj (R := S) M N)).inv ≫ evaluationMap M N =
        (adj.homEquiv _ N).symm t := by
    change _ ≫ ((SheafOfModules.tensorObjIsoSheafification M
      (SheafOfModules.homObj (R := S) M N)).hom ≫ _) = _
    rw [Iso.inv_hom_id_assoc]
    rfl
  have h := (adj.homEquiv _ N).apply_symm_apply t
  rw [Adjunction.homEquiv_unit, ← he] at h
  exact congrArg (fun f ↦ f.app X (x ⊗ₜ[S.obj.obj X] φ)) h

private theorem generator_eq (M N : Modules S) (X : Dᵒᵖ)
    (x : M.val.obj X) (y : N.val.obj X) :
    RingedForgetTensorTransposition.sheafTensorGenerator.{u, u, u} K S M N X x y =
      pureTensor M N X x y := rfl

attribute [local irreducible] pureTensor evaluationMap

/-- A sheaf-Hom evaluation pairing with the prescribed pure-tensor values is canonical.

Source: Stacks Project, Tags 03EK and 03EO: the sheaf tensor-Hom adjunction and evaluation.
(blueprint: lem-sf-twisted-action-evaluation-unique).

Proof: the tensor-Hom adjunction computes evaluationMap on a pure tensor x tensor phi
as phi applied to x. The sheafification adjunction transports this computation from
presheaves to sheaves. The right evaluation is the braiding followed by evaluationMap;
braiding interchanges the two pure factors. Both this composite and the given pairing
therefore have the prescribed values on all local pure tensors. Pure-tensor
extensionality, proved using the sheafification adjunction, identifies the two maps.
The argument applies on empty sites and to zero modules and zero coefficient rings. -/
theorem right_evaluation_eq (M N : Modules S)
    (e : SheafOfModules.homObj (R := S) M N ⊗ M ⟶ N)
    (h : RingedForgetTensorTransposition.IsSheafEvaluation.{u, u, u} K S M N e) :
    e = (β_ (SheafOfModules.homObj (R := S) M N) M).hom ≫ evaluationMap M N := by
  apply TensorRestriction.pure_ext
  intro X φ x
  change e.val.app X (pureTensor _ _ X φ x) =
    (evaluationMap M N).val.app X
      ((β_ (SheafOfModules.homObj (R := S) M N) M).hom.val.app X
        (pureTensor _ _ X φ x))
  have hh := h X φ x
  rw [generator_eq] at hh
  exact hh.trans ((evaluation_pure M N X x φ).symm.trans
    (congrArg ((evaluationMap M N).val.app X)
      (TensorRestriction.pure_braiding (SheafOfModules.homObj (R := S) M N) M X φ x)).symm)

end CategoryTheory.TwistedActionRingedSite
