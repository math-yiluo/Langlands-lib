/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Scalar coordinates on degree-zero unit cohomology

Source: Stacks Project, Cohomology, Tag 01DZ; Varieties, Tag 0BED.
(blueprint: lem-sc-scalar-unit-cohomology-coordinates).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The degree-zero cohomology class of the section 1, constructed using the canonical
map from sections to their zeroth right derived functor.
Source: Stacks Project, Cohomology, Tag 01DZ.
(blueprint: lem-sc-scalar-unit-cohomology-coordinates). -/
noncomputable def scalarUnitCohomologyClass {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) :
    scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) 0 :=
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
    (SheafOfModules.unit X.ringCatSheaf)).hom (1 : Γ(X, ⊤))

/-- Bijective structure maps give normalized scalar coordinates on degree-zero cohomology.
Source: Stacks Project, Cohomology, Tag 01DZ; Varieties, Tag 0BED.
(blueprint: lem-sc-scalar-unit-cohomology-coordinates).

Proof: Evaluation of module sheaves at the terminal open preserves finite limits.
Its zeroth right derived functor is therefore canonically isomorphic to evaluation.
Restrict this isomorphism along the structure ring map. The bijective structure map
is a linear equivalence from k to the sections of the unit module. Compose its inverse
with the degree-zero comparison. The inverse sends r to the class of the scalar section
r, which is r times the class of 1 by linearity. -/
theorem scalar_unit_cohomology_coordinates {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (h : Function.Bijective (scalarMap f ⊤)) :
    ∃ d : scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) 0 ≃ₗ[k] k,
      ∀ r : k, d.symm r = r • scalarUnitCohomologyClass f := by
  classical
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : PreservesFiniteLimits S := by
    dsimp [S, RingedSpace.globalSectionsFunctor]
    infer_instance
  let e := (ModuleCat.restrictScalars (scalarMap f ⊤)).mapIso
    (S.rightDerivedZeroIsoSelf.app (SheafOfModules.unit X.ringCatSheaf))
  let c := LinearEquiv.ofBijective (scalarUnitLinear f).hom h
  let d := e.toLinearEquiv.trans c.symm
  refine ⟨d, ?_⟩
  intro r
  have hc : c r = r • c 1 := by
    simpa only [smul_eq_mul, mul_one] using (c.map_smul r (1 : k))
  change e.inv.hom (c r) = r • scalarUnitCohomologyClass f
  rw [hc, e.inv.hom.map_smul]
  have hc1 : c 1 = (1 : Γ(X, ⊤)) := (scalarMap f ⊤).map_one
  rw [hc1]
  rfl

end AlgebraicGeometry.Scheme.Modules
