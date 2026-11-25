/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Extension by zero over the intrinsic constant coefficient sheaf

## References

* Stacks Project, Tags 03DI, 03DJ and 09AE
* Stacks, Tag 00YV
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The canonical realization equivalence extends fixed scalar actions to locally constant
scalar sections. Its inverse is the inverse of that fully faithful, essentially surjective
functor, not a freely chosen coefficient identification. -/
noncomputable def sfIntrinsicModuleEquivalence (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ≌
      proEtaleRingModules T (proEtaleConstantRing T A) :=
  letI := (ProEtale.finiteCoefficientIntrinsicRealization_exact T A).1
  (ProEtale.finiteCoefficientIntrinsicRealization T A).asEquivalence

/-- Extension by zero, in the intrinsic constant-ring presentation. On fixed-scalar sheaves,
the middle functor is left Kan extension along the localization followed by sheafification:
its sections are the unique summand indexed by a factorization through the open immersion,
or zero if there is no such factorization. The canonical realization equivalences extend
this same scalar action to the constant coefficient sheaves and transport both objects and
maps. -/
noncomputable def sfIntrinsicExtensionByZero {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    proEtaleRingModules U (proEtaleConstantRing U A) ⥤
      proEtaleRingModules X (proEtaleConstantRing X A) :=
  (sfIntrinsicModuleEquivalence U A).inverse ⋙
    ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
      (sfIntrinsicModuleEquivalence X A).functor

end AlgebraicGeometry.Scheme
