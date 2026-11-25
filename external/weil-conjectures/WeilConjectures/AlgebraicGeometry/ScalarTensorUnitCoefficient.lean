/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # ScalarTensorUnitCoefficient

Source: Stacks Project, Cohomology, Tag 0FKU.
(blueprint: lem-sc-scalar-tensor-unit-coefficient).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}}
attribute [local instance] Sheaf.monoidalCategory HasExt.standard

local instance scalarTensorMonoidal : MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  SheafOfModules.monoidalCategory X.sheaf

-- The sheafification unit and the constant-presheaf adjunction recover the scalar map.
private theorem scalarUnit_presheaf (f : X ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (r : k) :
    (scalarUnitMorphism f).hom.app (Opposite.op U)
      ((Functor.LaxMonoidal.ε (sheafToPresheaf (Opens.grothendieckTopology X)
        (ModuleCat.{u} k))).app (Opposite.op U) r) = scalarMap f U r := by
  let I := sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)
  let L := presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)
  let adj := CategoryTheory.sheafificationAdjunction
    (Opens.grothendieckTopology X) (ModuleCat.{u} k)
  have h : Functor.LaxMonoidal.ε I ≫ I.map (Functor.LaxMonoidal.ε L) =
      adj.unit.app (𝟙_ ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} k)) := by
    rw [← adj.unit_app_unit_comp_map_η, Category.assoc,
      ← I.map_comp, Functor.Monoidal.η_ε, I.map_id]
    exact Category.comp_id _
  have hc : Functor.LaxMonoidal.ε I ≫ (scalarUnitMorphism f).hom =
      ((constantPresheafAdj (ModuleCat.{u} k) isTerminalTop).homEquiv _ _).symm
        (scalarUnitLinear f) := by
    unfold scalarUnitMorphism constantScalarUnitIso
    change Functor.LaxMonoidal.ε I ≫
      I.map (Functor.LaxMonoidal.ε L ≫ _) = _
    rw [I.map_comp, ← Category.assoc, h]
    simp only [constantSheafAdj, Adjunction.comp_homEquiv, Equiv.symm_trans,
      Equiv.trans_apply]
    exact (adj.homEquiv _ _).apply_symm_apply _
  have hv := ConcreteCategory.congr_hom (NatTrans.congr_app hc (Opposite.op U)) r
  rw [Adjunction.homEquiv_counit] at hv
  change (scalarUnitMorphism f).hom.app (Opposite.op U)
      ((Functor.LaxMonoidal.ε I).app (Opposite.op U) r) =
    (X.presheaf.map (homOfLE (le_top (a := U))).op).hom (scalarMap f ⊤ r) at hv
  simpa [I, scalarMap] using hv

/-- Scalar tensor coefficients and the scalar unit respect both module unitors.
Source: Stacks Project, Modules, Tags 0096 and 01CA; Cohomology, Tag 0FKU.
(blueprint: lem-sc-scalar-tensor-unit-coefficient).

Proof: First identify the scalar unit on each open. Monoidal coherence for the
sheafification adjunction identifies its composite with the presheaf unit with
the constant-presheaf adjoint of scalarUnitLinear. The constant-presheaf counit
restricts the global scalar section, giving scalarMap f U r.
For the right identity, precompose with the inverse right unitor and apply
faithfulness of the sheaf inclusion. Its lax monoidal unit coherence and
naturality reduce the composite on a section s to the tensor coefficient on
s tensor the scalar-unit image of 1, followed by the module right unitor.
The scalar-unit formula and exists_scalarTensorCoefficient give tmulSection s 1.
The sectionwise right-unitor formula and one_smul return s. For the left identity,
precompose with the inverse left unitor and repeat with 1 tensor s and the
sectionwise left-unitor formula. Neither argument requires nonzero sections;
both apply to zero modules and the empty scheme. -/
theorem scalarTensorCoefficient_unit
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) :
    ((scalarSheaf f F) ◁ scalarUnitMorphism f) ≫
        scalarTensorCoefficient f F (SheafOfModules.unit X.ringCatSheaf) ≫
        scalarHom f (ρ_ F).hom = (ρ_ (scalarSheaf f F)).hom ∧
    (scalarUnitMorphism f ▷ (scalarSheaf f F)) ≫
        scalarTensorCoefficient f (SheafOfModules.unit X.ringCatSheaf) F ≫
        scalarHom f (λ_ F).hom = (λ_ (scalarSheaf f F)).hom := by
  let I := sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)
  constructor
  -- Precomposition by the inverse unitor reduces the tensor source to ordinary sections.
  · apply (cancel_epi (ρ_ (scalarSheaf f F)).inv).1
    rw [Iso.inv_hom_id]
    apply I.map_injective
    simp only [Functor.map_comp]
    rw [← Functor.LaxMonoidal.right_unitality_inv I (scalarSheaf f F)]
    simp only [Category.assoc]
    rw [← Functor.LaxMonoidal.μ_natural_right_assoc,
      ← whiskerLeft_comp_assoc]
    ext U s
    change (scalarHom f (ρ_ F).hom).hom.app U
      ((scalarTensorCoefficient f F (SheafOfModules.unit X.ringCatSheaf)).hom.app U
        ((Functor.LaxMonoidal.μ I (scalarSheaf f F)
          (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf))).app U
            (TensorProduct.tmul k s ((scalarUnitMorphism f).hom.app U
              ((Functor.LaxMonoidal.ε I).app U (1 : k)))))) = s
    rw [scalarUnit_presheaf f U.unop 1, exists_scalarTensorCoefficient]
    change (ρ_ F).hom.val.app U (tmulSection s (scalarMap f U.unop 1)) = s
    rw [map_one]
    change (ρ_ F).hom.app U.unop (tmulSection s (unitSectionsEquiv U.unop 1)) = s
    rw [rightUnitor_hom_app_tmulSection, one_smul]
  · apply (cancel_epi (λ_ (scalarSheaf f F)).inv).1
    rw [Iso.inv_hom_id]
    apply I.map_injective
    simp only [Functor.map_comp]
    rw [← Functor.LaxMonoidal.left_unitality_inv I (scalarSheaf f F)]
    simp only [Category.assoc]
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc,
      ← comp_whiskerRight_assoc]
    ext U s
    change (scalarHom f (λ_ F).hom).hom.app U
      ((scalarTensorCoefficient f (SheafOfModules.unit X.ringCatSheaf) F).hom.app U
        ((Functor.LaxMonoidal.μ I
          (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf)) (scalarSheaf f F)).app U
            (TensorProduct.tmul k ((scalarUnitMorphism f).hom.app U
              ((Functor.LaxMonoidal.ε I).app U (1 : k))) s))) = s
    rw [scalarUnit_presheaf f U.unop 1, exists_scalarTensorCoefficient]
    change (λ_ F).hom.val.app U (tmulSection (scalarMap f U.unop 1) s) = s
    rw [map_one]
    change (λ_ F).hom.app U.unop (tmulSection (unitSectionsEquiv U.unop 1) s) = s
    rw [leftUnitor_hom_app_tmulSection, one_smul]

end
end AlgebraicGeometry.Scheme.Modules
