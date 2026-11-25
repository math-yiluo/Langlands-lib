/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf

/-!
# Constructible finite-coefficient module sheaves on the pro-etale site

## References

* Stacks Project, Tag 09AJ (with an affine-local convention)

## Implementation details

We use global finite partitions with a positive number of strata. The restriction to a stratum
is `proEtaleConstantModulePullback`: inverse image followed by tensor extension along the
canonical comparison `proEtaleCoefficientInverseImageMap` of constant ring sheaves. Finiteness
is imposed on the underlying set of the module stalk, equivalently finite generation since the
coefficient ring is finite. The zero ring and the empty scheme are allowed.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A sheaf of modules over a finite commutative constant ring is constructible if
some finite partition into locally closed constructible immersed subschemes has
locally constant restrictions (via `proEtaleConstantModulePullback`) with finite geometric
stalks. -/
noncomputable def IsConstructibleProEtaleModuleSheaf
    (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) : Prop :=
  ∃ S : Stratification Y, 0 < S.n ∧
    ∀ i : Fin S.n,
      IsLocallyConstantProEtaleModuleSheaf (S.domain i) A
        (proEtaleConstantModulePullback (S.immersion i) A F) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (S.domain i) A)
          (proEtaleConstantModulePullback (S.immersion i) A F))

end AlgebraicGeometry.Scheme
