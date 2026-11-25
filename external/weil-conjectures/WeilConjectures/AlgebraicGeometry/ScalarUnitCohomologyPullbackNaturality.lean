/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyComparisonFamily
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.ScalarAbelianPullbackSquare
import WeilConjectures.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality
import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisExtFunctorSquare
import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic

/-! # Pullback compatibility of the explicit unit comparison

Source: Stacks Project, Tag 01F7.
(blueprint: new-sc-scalar-unit-pullback-naturality).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open Modules

/-- The explicit comparison map, rather than an arbitrary family of equivalences,
intertwines the two structure-sheaf pullback operations.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial and
cohomology-equation-choice; Tag 03FD, lemma-cohomology-modules-abelian-agree.
(blueprint: new-sc-scalar-unit-pullback-naturality).

Proof: Factor each explicit module-to-abelian comparison through scalar Ext.
Use coefficient naturality to move the tensor-unit coefficient map into Ext, and
cancel the cohomology-to-Ext equivalence with its inverse in the pullback formula.
The underlying abelian pullback square identifies the two coefficient maps and
the integer-unit classes. Apply naturality of Ext for this square of exact functors,
whose scalar Ext universes are u+1 and abelian Ext universes are u. Associativity
of Yoneda composition combines the unit and coefficient identities. The result
is the defining Ext formula for structureSheafCohomologyPullback. No injective
acyclicity assertion is needed for this algebraic reduction. -/
theorem scalar_unit_cohomology_pullback_naturality (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g)
    (x : scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) 1) :
    scalarUnitAbelianComparison Y
      (scalarCohomologyMap g (tensorPullbackObjUnitToUnit a) 1
        (scalarCohomologyPullback f g a h (SheafOfModules.unit X.ringCatSheaf) 1 x)) =
      structureSheafCohomologyPullback a 1 (scalarUnitAbelianComparison X x) := by
  -- The two independent Ext universes require repeated comparison-instance elaboration.
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let : MonoidalCategory (KSheaf X k) := Sheaf.monoidalCategory _ _
    let : MonoidalCategory (KSheaf Y k) := Sheaf.monoidalCategory _ _
    let : HasExt.{u + 1} (KSheaf X k) := HasExt.standard _
    let : HasExt.{u + 1} (KSheaf Y k) := HasExt.standard _
    rw [scalar_unit_abelian_ext_factorization k g,
      scalar_unit_abelian_ext_factorization k f, scalarCohomologyExtEquiv_map]
    unfold scalarCohomologyPullback
    rw [AddEquiv.apply_symm_apply]
    obtain ⟨c, hcunit, hccoeff⟩ := scalar_abelian_pullback_square k f g a h
    let z := scalarCohomologyExtEquiv f (SheafOfModules.unit X.ringCatSheaf) 1 x
    change scalarAbelianExtComparison k Y _ 1
        ((((Abelian.Ext.mk₀ (scalarInverseUnitIso a).inv).comp
          (z.mapExactFunctor (scalarInverseImage a)) (zero_add 1)).comp
          (Abelian.Ext.mk₀ (scalarPullbackCoefficient f g a h _)) (add_zero 1)).comp
          (Abelian.Ext.mk₀ (scalarHom g (tensorPullbackObjUnitToUnit a))) (add_zero 1)) = _
    unfold scalarAbelianExtComparison
    simp only [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
    simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
    rw [← Functor.map_comp, hccoeff]
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    rw [← Abelian.Ext.comp_assoc_of_third_deg_zero
      ((z.mapExactFunctor (scalarInverseImage a)).mapExactFunctor (scalarAbelianForget k Y))]
    erw [Abelian.Ext.mapExactFunctor_square.{u + 1, u + 1, u, u} (scalarInverseImage a)
      (scalarAbelianForget k X) (scalarAbelianForget k Y)
      (scalarAbelianInverseImage a) c 1 z]
    simp only [← Abelian.Ext.comp_assoc_of_third_deg_zero,
      ← Abelian.Ext.comp_assoc_of_second_deg_zero]
    erw [hcunit]
    rw [scalarAbelianStructurePullback_apply]
    rw [Abelian.Ext.mapExactFunctor_comp,
      Abelian.Ext.comp_assoc_of_second_deg_zero]

end AlgebraicGeometry.Scheme
