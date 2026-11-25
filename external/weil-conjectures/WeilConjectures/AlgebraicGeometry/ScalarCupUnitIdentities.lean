/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyCoordinates
import WeilConjectures.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality
import WeilConjectures.AlgebraicGeometry.ScalarUnitExtClass
import WeilConjectures.AlgebraicGeometry.ScalarTensorUnitCoefficient
import WeilConjectures.AlgebraicGeometry.ScalarExtCupDegreeZero
import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Cup with one on one scheme is the identity on structure-sheaf H1

Source: Stacks Project, Cohomology, Tags 0FKU and 01F7.
(blueprint: lem-sc-scalar-cup-unit-identities).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

noncomputable local instance instScalarCupUnitIdentitiesMonoidal (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Cup with the canonical class of one is the identity on structure-sheaf H¹.
Source: Stacks Project, Cohomology, section-cup-product, Lemma 20.31.1 (Tag 0FKU).
(blueprint: lem-sc-scalar-cup-unit-identities).

Proof: Evaluate morphisms from the structure sheaf at one in an injective resolution.
The augmentation representing the canonical degree-zero class corresponds to the
identity of the structure sheaf in degree-zero Ext. After restriction to k-vector
sheaves and precomposition by the scalar unit, its scalar Ext class is mk₀ of
scalarUnitMorphism. Expand scalarExtCup. Tensoring this degree-zero morphism on
either side and composing with scalarTensorCoefficient and the structure-sheaf
unitor gives the identity on the other coefficient: on sections the two composites
send s tensor one and one tensor s to s. The tensor universal property and the
sheafification adjunction give these equalities on sheaves. Naturality of the
unitors for exact-functor transport on Ext, and associativity of Ext composition,
and equality of the two unitors at the tensor unit
therefore reduce both products to the original Ext class. The cohomology-to-Ext
comparison is natural in coefficients, so transport this equality back along its
injective equivalence. Degree zero introduces no sign. This argument uses neither
an acyclic cover nor quasi-coherence. -/
theorem scalar_cup_unit_identities (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) :
    let U := SheafOfModules.unit X.ringCatSheaf
    (∀ a : scalarCohomology f U 1,
      scalarCohomologyMap f (λ_ U).hom 1
        (scalarCohomologyCup f U U 1 0 a (scalarUnitCohomologyClass f)) = a) ∧
    (∀ a : scalarCohomology f U 1,
      scalarCohomologyMap f (λ_ U).hom 1
        (scalarCohomologyCup f U U 0 1 (scalarUnitCohomologyClass f) a) = a) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      let U := SheafOfModules.unit X.ringCatSheaf
      let : MonoidalCategory (KSheaf X k) := Sheaf.monoidalCategory _ _
      let : HasExt.{u + 1} (KSheaf X k) := HasExt.standard (KSheaf X k)
      have hunit := scalarUnitCohomologyClass_ext f
      obtain ⟨hr, hl⟩ := scalarTensorCoefficient_unit f U
      have hr' :
          ((scalarSheaf f U) ◁ scalarUnitMorphism f) ≫
              scalarTensorCoefficient f U U ≫ scalarHom f (λ_ U).hom =
            (ρ_ (scalarSheaf f U)).hom := by
        have hρ : (ρ_ U).hom = (λ_ U).hom :=
          (unitors_equal (C := SheafOfModules.{u} X.ringCatSheaf)).symm
        simpa only [hρ] using hr
      constructor
      · intro a
        apply (scalarCohomologyExtEquiv f U 1).injective
        rw [scalarCohomologyExtEquiv_map]
        unfold scalarCohomologyCup
        change ((scalarCohomologyExtEquiv f (U ⊗ U) 1)
          ((scalarCohomologyExtEquiv f (U ⊗ U) 1).symm _)).comp _ _ = _
        rw [AddEquiv.apply_symm_apply, hunit]
        rw [(scalarExtCup_mk₀ (scalarCohomologyExtEquiv f U 1 a)
          (scalarUnitMorphism f)).1]
        simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
        simp only [Category.assoc]
        rw [hr']
        simp
      · intro a
        apply (scalarCohomologyExtEquiv f U 1).injective
        rw [scalarCohomologyExtEquiv_map]
        unfold scalarCohomologyCup
        change ((scalarCohomologyExtEquiv f (U ⊗ U) 1)
          ((scalarCohomologyExtEquiv f (U ⊗ U) 1).symm _)).comp _ _ = _
        rw [AddEquiv.apply_symm_apply, hunit]
        rw [(scalarExtCup_mk₀ (scalarCohomologyExtEquiv f U 1 a)
          (scalarUnitMorphism f)).2]
        simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
        simp only [Category.assoc]
        rw [hl]
        simp

end AlgebraicGeometry.Scheme.Modules
