/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-! # Extension by zero along an immersion

Source: Stacks Project, Tags 0E8I and 0A45
(blueprint: lem-sf-etale-generic-immersion-projection).

The functor `Rs_! = j_! Ri_*` for an immersion factored as a closed immersion `i` followed by
an open immersion `j`.
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The functor `Rs_! = j_! Ri_*` for the chosen closed-then-open factorization.
Source: Stacks Project, Tags 0E8I and 0A45
(blueprint: lem-sf-etale-generic-immersion-projection). -/
noncomputable abbrev immersionLowerShriek
    (A : Type (u + 1)) [CommRing A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  R((i)_*[ModuleCat.{u + 1} A]) ⋙ D((j)_!open[ModuleCat.{u + 1} A])

end AlgebraicGeometry.Etale
