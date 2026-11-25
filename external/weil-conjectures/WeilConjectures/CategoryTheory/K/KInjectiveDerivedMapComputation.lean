/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions

/-!
# Computing derived morphisms with arbitrary K-injective resolutions

Source: Stacks Project, Derived Categories, Tags 070I and 070Y, and the explicit
arbitrary-resolution consequence in the DAG (blueprint: lem-sf-kinjective-derived-map-computation).
The comparison is the recorded comparison of `def-sfb-right-derived-functor`.
All complexes are unbounded, and resolution maps need only be quasi-isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe wC wD vC vD uC uD

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable (F : C ⥤ D) [F.Additive]
  (enough : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)

end CategoryTheory.Functor
