/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientTensorCompatibility

/-! # Tensor comparison for an isomorphism of coefficient sheaves

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6, and Modules on Sites,
Tag 03EL. The comparison here concerns inverse image and tensor only.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

end AlgebraicGeometry.Scheme.CoefficientTensorTransport
