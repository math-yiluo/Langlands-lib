/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Open adjunction in the intrinsic finite constant-coefficient presentation

The existing exact site adjunction is transported by the canonical module equivalences,
then localized termwise on cochain complexes. This gives the full ordinary unbounded
adjunction without constructibility, Tor, or monoidal hypotheses on an intrinsic category.

## References

* Stacks Project, Tags 03DI, 03DJ and 09AE
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The open adjunction is the canonical site adjunction transported through the
constant-module equivalences and then descended termwise. -/
noncomputable def exceptionalOpenAdjunction
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] (A : Type u)
    [CommRing A] [Finite A] :
    sfIntrinsicDerivedOpen A j ⊣ sfIntrinsicDerivedPullback A j :=
  let adj : sfIntrinsicExtensionByZero j A ⊣ sfIntrinsicPullback A j :=
    sfIntrinsicOpenAdjunction A j
  letI : CatCommSq
      ((sfIntrinsicExtensionByZero j A).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (sfIntrinsicDerivedOpen A j) :=
    ⟨(sfIntrinsicExtensionByZero j A).mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq
      ((sfIntrinsicPullback A j).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (sfIntrinsicDerivedPullback A j) :=
    ⟨(sfIntrinsicPullback A j).mapDerivedCategoryFactors.symm⟩
  (adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (sfIntrinsicDerivedOpen A j) (sfIntrinsicDerivedPullback A j)

end AlgebraicGeometry.Scheme
