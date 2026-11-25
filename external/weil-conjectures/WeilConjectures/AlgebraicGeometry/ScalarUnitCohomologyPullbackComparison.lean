/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyPullbackNaturality

/-! # Module-to-abelian comparison for structure-sheaf pullbacks

Source: Stacks Project, Tags 03FD and 01F7, functoriality of cohomology.
(blueprint: lem-sc-scalar-unit-cohomology-pullback-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open Modules

/-- The module-to-abelian comparisons for unit coefficients can be chosen compatibly
with pullback along every morphism over the field. No cup product is involved.
Source: Stacks Project, Tag 03FD, lemma-cohomology-modules-abelian-agree;
Tag 01F7, cohomology-equation-functorial and cohomology-equation-choice.
(blueprint: lem-sc-scalar-unit-cohomology-pullback-comparison).

Proof: For every scheme choose an injective resolution of its unit module. Forgetting
modules is exact and forgotten injectives are acyclic for abelian sections (Tag 03FD).
Thus the same sections complex computes module and abelian cohomology. Restriction of
scalars leaves its additive group unchanged. The constant-integer sheaf adjunction
identifies abelian global sections cohomology with Ext, hence with Sheaf.H.
For a morphism a, use a lift of the adjoint structure-sheaf map to the resolutions.
The scalar inverse-image Ext operation followed by its coefficient map computes the
same pullback on the sections complex. Composing the coefficient map with the adjoint
unit isomorphism tensorPullbackObjUnitToUnit a gives precisely the structure-sheaf map.
After forgetting k-vector spaces, the exact inverse-image Ext operation computes the
abelian pullback recorded in structureSheafCohomologyPullback. The functoriality and
independence-of-lift assertions of Tag 01F7 identify both maps on cohomology. Use these
common-resolution comparisons for all schemes and structure morphisms simultaneously;
there is no separate choice for each naturality square. Empty schemes have zero
sections complexes and satisfy the same argument. -/
theorem scalar_unit_cohomology_pullback_comparison (k : Type u) [Field k] :
    ∃ e : ∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)),
      scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) 1 ≃+
        Sheaf.H (structureSheafAb X) 1,
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
        (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g)
        (x : scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) 1),
        e Y g (scalarCohomologyMap g (tensorPullbackObjUnitToUnit a) 1
          (scalarCohomologyPullback f g a h (SheafOfModules.unit X.ringCatSheaf) 1 x)) =
            structureSheafCohomologyPullback a 1 (e X f x) := by
  let e := fun (X : Scheme.{u}) (_f : X ⟶ Spec (CommRingCat.of k)) ↦
    AddEquiv.ofBijective (scalarUnitAbelianComparison X)
      (scalar_unit_abelian_comparison_bijective X)
  refine ⟨e, ?_⟩
  intro X Y f g a h x
  exact scalar_unit_cohomology_pullback_naturality k f g a h x

end AlgebraicGeometry.Scheme
