/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexCechData
public import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Tensor evaluation on the one-point ring site

The sheafification adjunction gives a natural tensor isomorphism after evaluation.
This module constructs that comparison and verifies its unit normalization.
Source: Stacks Project, More on Algebra, section-alternating-cech.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace CategoryTheory.RingPointTensorComparison

/-- The unique object at which module sheaves on the one-point ring site are evaluated.
Source: the tensor comparison and unit step of the localization tensor calculation,
Stacks Project, More on Algebra, section-alternating-cech.
(auxiliary; not a blueprint node). -/
abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

/-- Evaluation of a module sheaf at the unique object, expressed with explicit object and map
fields.
Source: the tensor comparison and unit step of the localization tensor calculation,
Stacks Project, More on Algebra, section-alternating-cech.
(auxiliary; not a blueprint node). -/
abbrev pointEval (A : CommRingCat.{u}) : RingSiteModules A ⥤ ModuleCat.{u} A :=
  { obj := fun M ↦ M.val.obj point
    map := fun f ↦ f.val.app point }

/-- Evaluation preserves addition of module morphisms, since their components add pointwise.
Source: the tensor comparison and unit step of the localization tensor calculation,
Stacks Project, More on Algebra, section-alternating-cech.
(auxiliary; not a blueprint node). -/
instance pointEval_additive (A : CommRingCat.{u}) : (pointEval A).Additive where
  map_add := by intros; rfl

/-- The tensor comparison obtained from the unit of sheafification and the inverse of the sheaf
tensor presentation.
Source: the tensor comparison and unit step of the localization tensor calculation,
Stacks Project, More on Algebra, section-alternating-cech.
(auxiliary; not a blueprint node). -/
def pointTensorMap {A : CommRingCat.{u}} (M N : RingSiteModules A) :
    M.val ⊗ N.val ⟶
      (letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
       M ⊗ N).val := by
  letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (M.val ⊗ N.val) ≫
    (SheafOfModules.tensorObjIsoSheafification
      (R := CochainComplex.onePointRingSheaf A) M N).inv.val

section
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification

/-- The comparison is invertible: every presheaf on the bottom topology is a sheaf, so the
sheafification unit is an isomorphism. Its other factor is the underlying inverse of an
isomorphism.
Source: the tensor comparison and unit step of the localization tensor calculation,
Stacks Project, More on Algebra, section-alternating-cech.
(auxiliary; not a blueprint node). -/
theorem pointTensorMap_isIso {A : CommRingCat.{u}} (M N : RingSiteModules A) :
    IsIso (pointTensorMap M N) := by
  let R := CochainComplex.onePointRingSheaf A
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
  have : IsIso (adj.unit.app (M.val ⊗ N.val)) :=
    adj.isIso_unit_app_of_iso (X := ⟨M.val ⊗ N.val, Presheaf.isSheaf_bot _⟩) (Iso.refl _)
  have : IsIso (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv.val :=
    ⟨⟨(SheafOfModules.tensorObjIsoSheafification (R := R) M N).hom.val,
      congrArg SheafOfModules.Hom.val
        (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv_hom_id,
      congrArg SheafOfModules.Hom.val
        (SheafOfModules.tensorObjIsoSheafification (R := R) M N).hom_inv_id⟩⟩
  change IsIso (adj.unit.app (M.val ⊗ N.val) ≫ _)
  infer_instance

end

attribute [local irreducible] pointTensorMap

/-- The evaluated tensor comparison, with inverse induced by the inverse presheaf comparison.
Source: the tensor comparison and unit step of the localization tensor calculation,
Stacks Project, More on Algebra, section-alternating-cech.
(auxiliary; not a blueprint node). -/
@[irreducible]
def pointTensorIso {A : CommRingCat.{u}} (M N : RingSiteModules A) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    (pointEval A).obj M ⊗ (pointEval A).obj N ≅ (pointEval A).obj (M ⊗ N) := by
  letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  let f := pointTensorMap M N
  letI : IsIso f := pointTensorMap_isIso M N
  exact
    { hom := f.app point
      inv := (inv f).app point
      hom_inv_id := congrArg (fun h ↦ h.app point) (IsIso.hom_inv_id f)
      inv_hom_id := congrArg (fun h ↦ h.app point) (IsIso.inv_hom_id f) }

private theorem pointTensorIso_hom {A : CommRingCat.{u}} (M N : RingSiteModules A) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    (pointTensorIso M N).hom = (pointTensorMap M N).app point := by
  delta pointTensorIso
  rfl

private theorem pointTensorMap_natural {A : CommRingCat.{u}}
    {M M' N N' : RingSiteModules A} (f : M ⟶ M') (g : N ⟶ N') :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    (f.val ⊗ₘ g.val) ≫ pointTensorMap M' N' =
      pointTensorMap M N ≫ (f ⊗ₘ g).val := by
  let R := CochainComplex.onePointRingSheaf A
  let := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification.{u}
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
  have h : (f ⊗ₘ g) ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) M' N').hom =
      (SheafOfModules.tensorObjIsoSheafification (R := R) M N).hom ≫
        S.map (f.val ⊗ₘ g.val) := by
    rw [tensorHom_def, Category.assoc,
      SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom (R := R) M' g,
      ← Category.assoc, SheafOfModules.whiskerRight_tensorObjIsoSheafification_hom (R := R) f N,
      Category.assoc, ← Functor.map_comp, ← tensorHom_def]
  have hi : (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv ≫
      (f ⊗ₘ g) = S.map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := R) M' N').inv := by
    rw [← cancel_mono (SheafOfModules.tensorObjIsoSheafification (R := R) M' N').hom]
    simp [Category.assoc, h]
  have hu := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.naturality
      (f.val ⊗ₘ g.val)
  dsimp at hu
  delta pointTensorMap
  rw [← Category.assoc, hu, Category.assoc]
  exact congrArg (fun z ↦ _ ≫ z) (congrArg SheafOfModules.Hom.val hi.symm)

private theorem pointTensorMap_unit {A : CommRingCat.{u}} (M : RingSiteModules A) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    pointTensorMap (ringComplexUnit A) M ≫ (λ_ M).hom.val = (λ_ M.val).hom := by
  let R := CochainComplex.onePointRingSheaf A
  let := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification.{u}
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
  have h : (SheafOfModules.tensorObjIsoSheafification (ringComplexUnit A) M).inv ≫
      (λ_ M).hom = S.map (λ_ M.val).hom ≫ adj.counit.app M := by
    let εM : S.obj M.val ⟶ M := adj.counit.app M
    change (Functor.OplaxMonoidal.δ S (𝟙_ _) M.val ≫
      (Functor.OplaxMonoidal.η S ⊗ₘ εM)) ≫ (λ_ M).hom = _
    rw [tensorHom_def, Category.assoc, Category.assoc, leftUnitor_naturality,
      ← Category.assoc, ← Category.assoc]
    simp only [Category.assoc]
    rw [← Functor.Monoidal.map_leftUnitor_assoc]
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  have he := congrArg (fun f ↦ f.val.app U
    ((adj.unit.app ((ringComplexUnit A).val ⊗ M.val)).app U x)) h
  have hu := congrArg (fun f ↦ f.app U x) (adj.unit.naturality (λ_ M.val).hom)
  have ht := congrArg (fun f ↦ f.app U ((λ_ M.val).hom.app U x))
    (adj.right_triangle_components M)
  change (λ_ M).hom.val.app U ((pointTensorMap (ringComplexUnit A) M).app U x) = _
  change _ = (adj.counit.app M).val.app U
    ((S.map (λ_ M.val).hom).val.app U
      ((adj.unit.app ((ringComplexUnit A).val ⊗ M.val)).app U x)) at he
  have hfinal := he.trans ((congrArg ((adj.counit.app M).val.app U) hu.symm).trans ht)
  simp only [Functor.id_obj, PresheafOfModules.id_app, ModuleCat.id_apply] at hfinal
  delta pointTensorMap
  convert hfinal using 1

section
variable (A : CommRingCat.{u})
local instance ringPointTensorComparisonInst1 : MonoidalCategory (RingSiteModules A) :=
  SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)

/-- Naturality of the evaluated tensor comparison. The two whiskering naturality formulas for the
sheaf tensor presentation and naturality of the sheafification unit give the presheaf square;
evaluate it at the point.
Source: the tensor comparison and unit step of the localization tensor calculation,
Stacks Project, More on Algebra, section-alternating-cech.
(auxiliary; not a blueprint node). -/
theorem pointTensorIso_natural {M M' N N' : RingSiteModules A}
    (f : M ⟶ M') (g : N ⟶ N') (t : (pointEval A).obj M ⊗[A] (pointEval A).obj N) :
    (pointEval A).map (f ⊗ₘ g) ((pointTensorIso M N).hom t) =
      (pointTensorIso M' N').hom
        (TensorProduct.map (f.val.app point).hom (g.val.app point).hom t) := by
  rw [pointTensorIso_hom, pointTensorIso_hom]
  exact (congrArg (fun h ↦ h.app point t) (pointTensorMap_natural f g)).symm

/-- The evaluated tensor comparison takes 1 tensor x to the inverse left unitor. Monoidality of
sheafification identifies the composite with the sheaf left unitor with the presheaf left
unitor; naturality of the adjunction unit and the triangle identity cancel sheafification. The
ordinary module unitor takes 1 tensor x to x, and is invertible.
Source: the tensor comparison and unit step of the localization tensor calculation,
Stacks Project, More on Algebra, section-alternating-cech.
(auxiliary; not a blueprint node). -/
theorem pointTensorIso_unit (M : RingSiteModules A)
    (x : (pointEval A).obj M) :
    (pointTensorIso (ringComplexUnit A) M).hom ((1 : A) ⊗ₜ[A] x) =
      (pointEval A).map (λ_ M).inv x := by
  have h : (pointEval A).map (λ_ M).hom
      ((pointTensorIso (ringComplexUnit A) M).hom ((1 : A) ⊗ₜ[A] x)) = x := by
    rw [pointTensorIso_hom]
    have h := congrArg (fun h ↦ h.app point ((1 : A) ⊗ₜ[A] x)) (pointTensorMap_unit M)
    change (pointEval A).map (λ_ M).hom
      ((pointTensorMap (ringComplexUnit A) M).app point ((1 : A) ⊗ₜ[A] x)) =
        (λ_ ((pointEval A).obj M)).hom ((1 : A) ⊗ₜ[A] x) at h
    exact h.trans (by change (1 : A) • x = x; exact one_smul A x)
  exact ((pointEval A).mapIso (λ_ M)).toLinearEquiv.injective
    (h.trans (((pointEval A).mapIso (λ_ M)).toLinearEquiv.apply_symm_apply x).symm)
end

end CategoryTheory.RingPointTensorComparison
