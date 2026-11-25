/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TensorRestriction.TwistedActionTensorRestrictionSupplement
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionInclusionCocontinuous

/-! # Normalized tensor comparisons for action-site restriction

Source: steps 9--10 and the tensor part of step 13 of the twisted Stacks 00W0 argument.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

open TensorRestriction

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Only the tensor and unit part of a full action-site presentation.
Source: steps 9--10 and the tensor part of step 13 of the twisted Stacks 00W0 argument
(blueprint: lem-sf-twisted-action-tensor-comparisons). -/
structure TensorComparisons (P : RestrictionPresentation J s R a) where
  /-- The restriction of the sheaf tensor is the ordinary sheaf tensor. -/
  tensor :
    letI := P.category
    ∀ (M N : Modules P.coefficient),
      (P.modules.functor.obj (tensorObj M N)).obj.a ≅
      tensorObj (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a
  /-- Translation's tensor comparison. -/
  sigmaTensor :
    letI := P.category
    ∀ (M N : Modules R),
      (sigma J s R a).obj (tensorObj M N) ≅
      tensorObj ((sigma J s R a).obj M) ((sigma J s R a).obj N)
  /-- Restriction keeps the local pure tensors that define the sheaf tensor. -/
  tensor_pure :
    letI := P.category
    ∀ (M N : Modules P.coefficient) (X : Cᵒᵖ)
      (x : (P.modules.functor.obj M).obj.a.val.obj X)
      (y : (P.modules.functor.obj N).obj.a.val.obj X),
      (P.restriction.hom.app (tensorObj M N)).val.app X
        ((tensor M N).inv.val.app X
          (pureTensor (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a X x y)) =
      pureTensor M N (P.inclusion.op.obj X)
        ((P.restriction.hom.app M).val.app X x) ((P.restriction.hom.app N).val.app X y)
  /-- Translation's tensor comparison has the canonical pure-tensor normalization. -/
  sigmaTensor_pure :
    letI := P.category
    ∀ (M N : Modules R) (X : Cᵒᵖ)
      (x : M.val.obj (s.inverse.op.obj X)) (y : N.val.obj (s.inverse.op.obj X)),
      (sigmaTensor M N).hom.val.app X (pureTensor M N (s.inverse.op.obj X) x y) =
      pureTensor ((sigma J s R a).obj M) ((sigma J s R a).obj N) X x y
  /-- The tensor action is the diagonal action under these comparisons. -/
  tensor_action :
    letI := P.category
    ∀ (M N : Modules P.coefficient),
      (P.modules.functor.obj (tensorObj M N)).obj.str ≫ (tensor M N).hom =
      (sigma J s R a).map (tensor M N).hom ≫
        (sigmaTensor (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a).hom ≫
          tensorMap (P.modules.functor.obj M).obj.str (P.modules.functor.obj N).obj.str
  /-- The tensor unit restricts to R. -/
  unit :
    letI := P.category
    (P.modules.functor.obj (𝟙_ (Modules P.coefficient))).obj.a ≅ 𝟙_ (Modules R)
  /-- On the unit, the comparison is the coefficient restriction itself. -/
  unit_sections :
    letI := P.category
    ∀ (X : Cᵒᵖ)
      (x : (P.modules.functor.obj (𝟙_ (Modules P.coefficient))).obj.a.val.obj X),
      unit.hom.val.app X x =
      (P.coefficientRestriction.hom.hom.app X)
        ((P.restriction.hom.app (𝟙_ (Modules P.coefficient))).val.app X x)
  /-- The action on the unit is the originally chosen ring action. -/
  sigmaUnit :
    letI := P.category
    (sigma J s R a).obj (𝟙_ (Modules R)) ≅ 𝟙_ (Modules R)
  /-- The original ring isomorphism specifies the unit action on local sections. -/
  sigmaUnit_sections :
    letI := P.category
    ∀ (X : C) (r : R.obj.obj (op (s.inverse.obj X))),
      sigmaUnit.hom.val.app (op X) r = (a.hom.hom.app (op X)) r
  /-- The unit comparison intertwines precisely this action. -/
  unit_action :
    letI := P.category
    (P.modules.functor.obj (𝟙_ (Modules P.coefficient))).obj.str ≫ unit.hom =
    (sigma J s R a).map unit.hom ≫ sigmaUnit.hom
  /-- The tensor identifications are natural in both sheaves. -/
  tensor_naturality :
    letI := P.category
    ∀ {M M' N N' : Modules P.coefficient} (f : M ⟶ M') (g : N ⟶ N'),
      (P.modules.functor.map (tensorMap f g)).hom.f ≫ (tensor M' N').hom =
      (tensor M N).hom ≫
        tensorMap (P.modules.functor.map f).hom.f (P.modules.functor.map g).hom.f
  /-- Translation's tensor comparisons are natural in both modules. -/
  sigmaTensor_naturality :
    letI := P.category
    ∀ {M M' N N' : Modules R} (f : M ⟶ M') (g : N ⟶ N'),
      (sigma J s R a).map (tensorMap f g) ≫ (sigmaTensor M' N').hom =
      (sigmaTensor M N).hom ≫
        tensorMap ((sigma J s R a).map f) ((sigma J s R a).map g)
  /-- Tensor symmetry is respected. -/
  symmetry :
    letI := P.category
    ∀ (M N : Modules P.coefficient),
      (P.modules.functor.map (β_ M N).hom).hom.f ≫ (tensor N M).hom =
      (tensor M N).hom ≫ (β_ (P.modules.functor.obj M).obj.a
        (P.modules.functor.obj N).obj.a).hom

private noncomputable def restrictedTensorIso [HasPullbacks C]
    (P : RestrictionPresentation J s R a) :
    letI := P.category
    ∀ M N : Modules P.coefficient,
      (P.modules.functor.obj (tensorObj M N)).obj.a ≅
        tensorObj (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a := by
  letI := P.category
  letI := P.inclusion_continuous
  intro M N
  have : P.inclusion.IsCocontinuous J P.topology :=
    inclusion_cocontinuous J s R a P.toSite
  have h Q := restrictionSheafificationMap_isIso
    (coefficientMap P.inclusion P.coefficient R P.coefficientRestriction) Q
  have := tensorPushMap_isIso P.inclusion P.coefficient R P.coefficientRestriction h M N
  exact P.restriction.app (tensorObj M N) ≪≫
    (asIso (tensorPushMap P.inclusion P.coefficient R P.coefficientRestriction M N)).symm ≪≫
      (P.restriction.app M ⊗ᵢ P.restriction.app N).symm

private theorem restrictedTensorIso_pure [HasPullbacks C]
    (P : RestrictionPresentation J s R a) :
    letI := P.category
    ∀ (M N : Modules P.coefficient) (X : Cᵒᵖ)
      (x : (P.modules.functor.obj M).obj.a.val.obj X)
      (y : (P.modules.functor.obj N).obj.a.val.obj X),
      (P.restriction.hom.app (tensorObj M N)).val.app X
        ((restrictedTensorIso J s R a P M N).inv.val.app X (pureTensor _ _ X x y)) =
      pureTensor M N (P.inclusion.op.obj X)
        ((P.restriction.hom.app M).val.app X x)
        ((P.restriction.hom.app N).val.app X y) := by
  let := P.category
  let := P.inclusion_continuous
  intro M N X x y
  change (P.restriction.hom.app (tensorObj M N)).val.app X
    ((P.restriction.inv.app (tensorObj M N)).val.app X
      ((tensorPushMap P.inclusion P.coefficient R P.coefficientRestriction M N).val.app X
        ((tensorMap (P.restriction.hom.app M) (P.restriction.hom.app N)).val.app X
          (pureTensor _ _ X x y)))) = _
  erw [sheaf_iso_inv_hom_apply (P.restriction.app _)]
  rw [pure_map, tensorPushMap_pure]

private noncomputable def translatedTensorIso (M N : Modules R) :
    (sigma J s R a).obj (tensorObj M N) ≅
      tensorObj ((sigma J s R a).obj M) ((sigma J s R a).obj N) := by
  have : s.inverse.IsCocontinuous J J :=
    (s.symm.toAdjunction.isCocontinuous_iff_coverPreserving J J).2
      (CoverPreserving.of_isContinuous s.functor J J)
  have h Q := restrictionSheafificationMap_isIso
    (coefficientMap s.inverse R R a) Q
  have := tensorPushMap_isIso s.inverse R R a h M N
  exact (asIso (tensorPushMap s.inverse R R a M N)).symm

private theorem translatedTensorIso_pure (M N : Modules R) (X : Cᵒᵖ)
    (x : M.val.obj (s.inverse.op.obj X)) (y : N.val.obj (s.inverse.op.obj X)) :
    (translatedTensorIso J s R a M N).hom.val.app X
      (pureTensor M N (s.inverse.op.obj X) x y) =
    pureTensor ((sigma J s R a).obj M) ((sigma J s R a).obj N) X x y := by
  have h := tensorPushMap_pure s.inverse R R a M N X x y
  exact (congrArg ((translatedTensorIso J s R a M N).hom.val.app X) h).symm.trans
    (sheaf_iso_inv_hom_apply (translatedTensorIso J s R a M N) X _)

private noncomputable def restrictedUnitIso (P : RestrictionPresentation J s R a) :
    letI := P.category
    (P.modules.functor.obj (𝟙_ (Modules P.coefficient))).obj.a ≅ 𝟙_ (Modules R) :=
by
  letI := P.category
  letI := P.inclusion_continuous
  exact P.restriction.app _ ≪≫
    restrictionUnitIso P.inclusion P.coefficient R P.coefficientRestriction

private noncomputable def translatedUnitIso :
    (sigma J s R a).obj (𝟙_ (Modules R)) ≅ 𝟙_ (Modules R) :=
  restrictionUnitIso s.inverse R R a

omit [s.functor.IsContinuous J J] in
private theorem restriction_naturality_apply (P : RestrictionPresentation J s R a) :
    letI := P.category
    ∀ {M N : Modules P.coefficient} (f : M ⟶ N) (X : Cᵒᵖ)
      (x : (P.modules.functor.obj M).obj.a.val.obj X),
      (P.restriction.hom.app N).val.app X
        ((P.modules.functor.map f).hom.f.val.app X x) =
      f.val.app (P.inclusion.op.obj X) ((P.restriction.hom.app M).val.app X x) := by
  let := P.category
  let := P.inclusion_continuous
  intro M N f X x
  exact congrArg (fun k ↦ k.val.app X x) (P.restriction.hom.naturality f)

omit [s.functor.IsContinuous J J] in
private theorem generator_injective (P : RestrictionPresentation J s R a) :
    letI := P.category
    ∀ (M : Modules P.coefficient) (X : C),
      Function.Injective (M.val.map
        ((P.arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op) := by
  let := P.category
  let := P.inclusion_continuous
  intro M X
  let T := P.modules.functor.obj M
  let r := P.restriction.app M
  have he (z : M.val.obj (op (P.inclusion.obj X))) :
      M.val.map ((P.arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op z =
      r.hom.val.app (op (s.inverse.obj X))
        ((pairIso T).inv.val.app (op X) (r.inv.val.app (op X) z)) := by
    have h := P.module_generator M X
      ((pairIso T).inv.val.app (op X) (r.inv.val.app (op X) z))
    change _ = M.val.map _
      (r.hom.val.app (op X) ((pairIso T).hom.val.app (op X)
        ((pairIso T).inv.val.app (op X) (r.inv.val.app (op X) z)))) at h
    rw [sheaf_iso_inv_hom_apply, sheaf_iso_inv_hom_apply] at h
    exact h.symm
  intro x y h
  rw [he, he] at h
  apply iso_section_injective r.symm (op X)
  apply iso_section_injective (pairIso T).symm (op X)
  apply iso_section_injective r (op (s.inverse.obj X))
  exact h

private theorem restrictedTensorIso_natural [HasPullbacks C]
    (P : RestrictionPresentation J s R a) :
    letI := P.category
    ∀ {M M' N N' : Modules P.coefficient} (f : M ⟶ M') (g : N ⟶ N'),
      (P.modules.functor.map (tensorMap f g)).hom.f ≫
          (restrictedTensorIso J s R a P M' N').hom =
        (restrictedTensorIso J s R a P M N).hom ≫
          tensorMap (P.modules.functor.map f).hom.f (P.modules.functor.map g).hom.f := by
  let := P.category
  let := P.inclusion_continuous
  intro M M' N N' f g
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  apply pure_ext
  intro X x y
  apply iso_section_injective (P.restriction.app _) X
  change (P.restriction.hom.app _).val.app X
      ((P.modules.functor.map (tensorMap f g)).hom.f.val.app X
        ((restrictedTensorIso J s R a P M N).inv.val.app X (pureTensor _ _ X x y))) =
    (P.restriction.hom.app _).val.app X
      ((restrictedTensorIso J s R a P M' N').inv.val.app X
        ((tensorMap _ _).val.app X (pureTensor _ _ X x y)))
  simp only [restriction_naturality_apply, restrictedTensorIso_pure, pure_map]

private theorem restrictedTensorIso_symmetry [HasPullbacks C]
    (P : RestrictionPresentation J s R a) :
    letI := P.category
    ∀ M N : Modules P.coefficient,
      (P.modules.functor.map (β_ M N).hom).hom.f ≫
          (restrictedTensorIso J s R a P N M).hom =
        (restrictedTensorIso J s R a P M N).hom ≫
          (β_ (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a).hom := by
  let := P.category
  let := P.inclusion_continuous
  intro M N
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  apply pure_ext
  intro X x y
  apply iso_section_injective (P.restriction.app _) X
  change (P.restriction.hom.app _).val.app X
      ((P.modules.functor.map (β_ M N).hom).hom.f.val.app X
        ((restrictedTensorIso J s R a P M N).inv.val.app X (pureTensor _ _ X x y))) =
    (P.restriction.hom.app _).val.app X
      ((restrictedTensorIso J s R a P N M).inv.val.app X
        ((β_ (P.modules.functor.obj M).obj.a
          (P.modules.functor.obj N).obj.a).hom.val.app X (pureTensor _ _ X x y)))
  simp only [restriction_naturality_apply, restrictedTensorIso_pure, pure_braiding]

private theorem translatedTensorIso_natural {M M' N N' : Modules R}
    (f : M ⟶ M') (g : N ⟶ N') :
    (sigma J s R a).map (tensorMap f g) ≫ (translatedTensorIso J s R a M' N').hom =
      (translatedTensorIso J s R a M N).hom ≫
        tensorMap ((sigma J s R a).map f) ((sigma J s R a).map g) := by
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  exact (tensorPushMap_natural s.inverse R R a f g).symm

private theorem restrictedTensorIso_action [HasPullbacks C]
    (P : RestrictionPresentation J s R a) :
    letI := P.category
    ∀ M N : Modules P.coefficient,
      (P.modules.functor.obj (tensorObj M N)).obj.str ≫
          (restrictedTensorIso J s R a P M N).hom =
        (sigma J s R a).map (restrictedTensorIso J s R a P M N).hom ≫
          (translatedTensorIso J s R a
            (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a).hom ≫
            tensorMap (P.modules.functor.obj M).obj.str (P.modules.functor.obj N).obj.str := by
  let := P.category
  let := P.inclusion_continuous
  intro M N
  let t := restrictedTensorIso J s R a P M N
  let b := translatedTensorIso J s R a
    (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a
  change _ ≫ t.hom = (sigma J s R a).map t.hom ≫ b.hom ≫ _
  rw [← Iso.eq_comp_inv]
  apply (cancel_epi (b.inv ≫ (sigma J s R a).map t.inv)).mp
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_assoc]
  apply pure_ext
  intro X x y
  apply iso_section_injective (P.restriction.app _) X
  apply generator_injective J s R a P (tensorObj M N) X.unop
  change (tensorObj M N).val.map
      ((P.arrows (s.inverse.obj X.unop) X.unop).symm ⟨-1, 𝟙 _⟩).op
      ((P.restriction.hom.app _).val.app X
        ((P.modules.functor.obj (tensorObj M N)).obj.str.val.app X
          (t.inv.val.app (s.inverse.op.obj X)
            (b.inv.val.app X (pureTensor _ _ X x y))))) =
    (tensorObj M N).val.map
      ((P.arrows (s.inverse.obj X.unop) X.unop).symm ⟨-1, 𝟙 _⟩).op
      ((P.restriction.hom.app _).val.app X
        (t.inv.val.app X
          ((tensorMap (P.modules.functor.obj M).obj.str
            (P.modules.functor.obj N).obj.str).val.app X (pureTensor _ _ X x y))))
  have hb : b.inv.val.app X (pureTensor _ _ X x y) =
      pureTensor (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a
        (s.inverse.op.obj X) x y :=
    tensorPushMap_pure s.inverse R R a _ _ X x y
  rw [hb, ← P.module_generator]
  change (P.restriction.hom.app _).val.app (s.inverse.op.obj X)
      ((restrictedTensorIso J s R a P M N).inv.val.app (s.inverse.op.obj X)
        (pureTensor _ _ (s.inverse.op.obj X) x y)) = _
  rw [restrictedTensorIso_pure, pure_map]
  change _ = (tensorObj M N).val.map _
    ((P.restriction.hom.app _).val.app X
      ((restrictedTensorIso J s R a P M N).inv.val.app X (pureTensor _ _ X _ _)))
  rw [restrictedTensorIso_pure, pure_restrict]
  exact congrArg₂ (pureTensor M N (P.inclusion.op.obj (s.inverse.op.obj X)))
    (P.module_generator M X.unop x) (P.module_generator N X.unop y)

omit [s.functor.IsContinuous J J] in
private theorem restrictedUnitIso_action (P : RestrictionPresentation J s R a) :
    letI := P.category
    (P.modules.functor.obj (𝟙_ (Modules P.coefficient))).obj.str ≫
        (restrictedUnitIso J s R a P).hom =
      (sigma J s R a).map (restrictedUnitIso J s R a P).hom ≫
        (translatedUnitIso J s R a).hom := by
  let := P.category
  let := P.inclusion_continuous
  ext X x
  change (P.coefficientRestriction.hom.hom.app X)
      ((P.restriction.hom.app _).val.app X
        ((P.modules.functor.obj (𝟙_ (Modules P.coefficient))).obj.str.val.app X x)) =
    (a.hom.hom.app X)
      ((P.coefficientRestriction.hom.hom.app (s.inverse.op.obj X))
        ((P.restriction.hom.app _).val.app (s.inverse.op.obj X) x))
  have hg := P.module_generator (𝟙_ (Modules P.coefficient)) X.unop x
  have hc := P.coefficient_generator X.unop
    ((P.restriction.hom.app _).val.app X
      ((P.modules.functor.obj (𝟙_ (Modules P.coefficient))).obj.str.val.app X x))
  change (P.coefficientRestriction.hom.hom.app (s.inverse.op.obj X))
    (((𝟙_ (Modules P.coefficient)).val.map _ )
      ((P.restriction.hom.app _).val.app X
        ((P.modules.functor.obj (𝟙_ (Modules P.coefficient))).obj.str.val.app X x))) = _ at hc
  erw [← hg] at hc
  have h := congrArg (a.hom.hom.app X) hc
  have ha (z : R.obj.obj X) :
      a.hom.hom.app X (a.inv.hom.app X z) = z :=
    congrArg (fun k ↦ k.hom.app X z) a.inv_hom_id
  exact (ha _).symm.trans h.symm

attribute [irreducible] restrictedTensorIso translatedTensorIso

/-- Restriction and translation preserve the normalized tensor and unit.
Source: steps 9--10 and the tensor part of step 13 of the twisted Stacks 00W0 argument;
Stacks 03EK for the sheafified sectionwise tensor.
(blueprint: lem-sf-twisted-action-tensor-comparisons).

Proof: the degree-zero inclusion is continuous and cocontinuous. Restriction therefore
preserves local injectivity and local surjectivity of presheaf morphisms. Transpose the
restricted module-sheafification unit along the source sheafification adjunction. Its
composite with the source unit is the restricted target unit, so local bijectivity shows
that this transpose is an isomorphism of sheaves. Apply it to the sectionwise tensor,
composing with sheafification of the scalar-restriction tensorator and the canonical
sheaf-tensor isomorphisms. The scalar-restriction tensorator is invertible because the
coefficient map is an isomorphism: tensor the semilinear identity equivalences of its
two factors. The unit equation computes the composite on pure tensors. Transport the
result through P.restriction to obtain tensor and its displayed normalization.
Inverse-site translation is cocontinuous by continuity of the forward equivalence;
the same construction gives sigmaTensor and its normalization. The coefficient
isomorphisms give explicit linear equivalences of the rank-one modules, hence unit and
sigmaUnit with precisely the prescribed section maps. The coefficient-generator and
module-generator equations prove unit_action. Maps out of a sheaf tensor are determined
on pure tensors by the sheafification adjunction, proving naturality and symmetry.
For tensor_action, cancel the tensor comparisons, test on pure tensors, and apply the
degree-minus-one generator restriction. This restriction is injective because the
module-generator equation expresses it through the invertible pair action and the
sectionwise restriction isomorphisms. The resulting equality is the pure-tensor
restriction formula and the module-generator equation for each factor. No induction,
internal-Hom or exactness data are used. Empty sites and the zero ring require no change.
-/
theorem tensorComparisons [HasPullbacks C] (P : RestrictionPresentation J s R a) :
    Nonempty (TensorComparisons J s R a P) := by
  let := P.category
  let := P.inclusion_continuous
  exact ⟨{
    tensor := restrictedTensorIso J s R a P
    sigmaTensor := translatedTensorIso J s R a
    tensor_pure := restrictedTensorIso_pure J s R a P
    sigmaTensor_pure := translatedTensorIso_pure J s R a
    tensor_action := restrictedTensorIso_action J s R a P
    unit := restrictedUnitIso J s R a P
    unit_sections := fun _ _ ↦ rfl
    sigmaUnit := translatedUnitIso J s R a
    sigmaUnit_sections := fun _ _ ↦ rfl
    unit_action := restrictedUnitIso_action J s R a P
    tensor_naturality := restrictedTensorIso_natural J s R a P
    sigmaTensor_naturality := translatedTensorIso_natural J s R a
    symmetry := restrictedTensorIso_symmetry J s R a P }⟩

end CategoryTheory.TwistedActionRingedSite
