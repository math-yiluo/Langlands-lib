/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Betti numbers of derived residue-field fibres

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.31.1, Tag 0BDI
(blueprint: def-sc-derived-fiber-betti).

On the one-point scheme `Spec κ(x)`, evaluation of the cohomology sheaf on the whole
space gives its cohomology vector space. Scalars are transported along `ΓSpecIso`.
-/

@[expose] public section

universe u w

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The degree-`i` cohomology vector space of the derived fibre `Li_x^* E`.
It is the global sections of its cohomology sheaf on `Spec κ(x)`, with the canonical
`κ(x)`-action via the inverse of `ΓSpecIso`.
Source: Stacks Project, Tag 0BDI (blueprint: def-sc-derived-fiber-betti). -/
noncomputable def derivedFiberCohomology (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (i : ℤ) (x : X)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))] :
    ModuleCat.{u} (X.residueField x) :=
  (ModuleCat.restrictScalars (ΓSpecIso (X.residueField x)).inv.hom).obj
    ((SheafOfModules.evaluation
      (moduleRings (Spec (X.residueField x)).toRingedSpace) (op ⊤)).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (X.residueField x)).toRingedSpace)) i).obj
          ((derivedPullback (X.fromSpecResidueField x)).obj E)))

/-- The Betti number `β_i(x) = dim_{κ(x)} H^i(Li_x^* E)` for a pseudo-coherent complex.
The formula is defined for every derived object; pseudo-coherence ensures that the
cohomology vector spaces are finite dimensional.
Source: Stacks Project, Tag 0BDI (blueprint: def-sc-derived-fiber-betti). -/
noncomputable def derivedFiberBetti (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (i : ℤ) (x : X) : ℕ :=
  Module.finrank (X.residueField x) (derivedFiberCohomology X E i x)

end AlgebraicGeometry.Scheme
