/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.SectionwiseFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

/-! # Finite scalar local models on a profinite slice

This is the profinite-slice companion of the imported scheme-site predicate. A finite
presentation on the condensed point is a cokernel of a finite scalar matrix: maps between
finite free regular modules are matrices over the sections at the one-point space.
Its slice pullback is therefore exactly scalar extension from discrete constant scalars.
The covering sieve permits different scalar presentations on its different members.

## References

* Hemo--Richarz--Scholbach, Remark 3.2 and Definition 3.5
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale
