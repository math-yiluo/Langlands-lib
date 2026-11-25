/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

/-! # The existing signed Tate twists in internal module notation

The underlying coefficient lines and all their transitions are unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Transport the recorded signed line back along the section-module equivalence.
This equivalence retains the underlying sheaf and coefficient action; no new line
or trivialization is chosen. -/
def spInternalSignedTwist (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (d : ℤ) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X) R).inverse.obj
    (spSignedTwist X R L d)

/-- Derived tensor with the recorded signed line in degree zero, in the ordinary
unbounded internal-module category. -/
def spInternalComplexTwist (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) (d : ℤ) :=
  K ⊗ (DerivedCategory.singleFunctor _ 0).obj (spInternalSignedTwist X R L d)

end AlgebraicGeometry.ProEtale
