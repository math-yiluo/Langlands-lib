/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# The right derived functor of a linear functor is linear

Let `F : C ⥤ D` be an `R`-linear functor between `R`-linear abelian categories, where `C` has
K-injective resolutions. The right derived functor `F.rightDerivedFunctor : D(C) ⥤ D(D)` is
`R`-linear: it is the inverse of the equivalence `K(Inj) ≌ D(C)` followed by `F` applied
termwise (`CategoryTheory.Functor.rightDerivedFunctorIsoKInjectives`), and all these functors
are `R`-linear.
-/

@[expose] public section

open CategoryTheory Abelian

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
  (R : Type*) [Ring R] [CategoryTheory.Linear R C]
  [CategoryTheory.Linear R D] (F : C ⥤ D) [F.Additive] [F.Linear R]

/-- The right derived functor of an `R`-linear functor is `R`-linear. -/
instance linear_rightDerivedFunctor : F.rightDerivedFunctor.Linear R :=
  have : (HomotopyCategory.KInjectives.equivalence C).functor.Linear R :=
    inferInstanceAs ((ObjectProperty.ι _ ⋙ DerivedCategory.Qh).Linear R)
  Functor.linear_of_iso _ F.rightDerivedFunctorIsoKInjectives.symm

end CategoryTheory.Functor
