/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti

/-! # Functorial derived residue-field cohomology

Source: Stacks Project, Tags 06YJ and 0BDI.
(blueprint: new-derived-fiber-cohomology-functor)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Derived residue pullback, homology, sections and the canonical residue-field action.
This is the functor whose object value is `derivedFiberCohomology`.
Source: Stacks Project, Tags 06YJ and 0BDI.
(blueprint: new-derived-fiber-cohomology-functor) -/
noncomputable def derivedFiberCohomologyFunctor (W : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toRingedSpace))]
    (w : W) (i : ℤ)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (W.residueField w)).toRingedSpace))] :
    schemeDerivedCategory W ⥤ ModuleCat.{u} (W.residueField w) :=
  derivedPullback (W.fromSpecResidueField w) ⋙
    DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (W.residueField w)).toRingedSpace)) i ⋙
    SheafOfModules.evaluation
      (moduleRings (Spec (W.residueField w)).toRingedSpace) (.op ⊤) ⋙
    ModuleCat.restrictScalars (ΓSpecIso (W.residueField w)).inv.hom

end AlgebraicGeometry.Scheme
