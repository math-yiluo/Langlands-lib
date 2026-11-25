/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.AlgebraicGeometry.FiniteRingProperEtaleCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Proper étale pushforward with finite ring coefficients

Source: latest blueprint, chap-Construction-of-f, theorem-existence-exceptional-inverse-image, order
2549; Stacks Project, Tags 0F0D and 0F5Y
(blueprint: theorem-existence-exceptional-inverse-image--1).

The coefficient ring need not be commutative. The recorded upstream instance requires
`CommRing`, so it cannot supply the noncommutative instances of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

private theorem finiteRing_brown
    (Λ : Type (u + 1)) [Ring Λ]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (hcoprod : ∀ I : Type (u + 1),
      CategoryTheory.Limits.PreservesColimitsOfShape (Discrete I)
        (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor) :
    (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.IsLeftAdjoint := by
  let : Limits.HasCoproducts.{u + 1}
      (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    derived_hasCoproducts
  let : Limits.HasCoproducts.{u + 1}
      (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    derived_hasCoproducts
  exact grothendieckDerived_hasRightAdjoint _ hcoprod

/-- Proper pushforward on unbounded derived categories of étale sheaves of modules over
any finite ring has a right adjoint.
Source: latest blueprint, order 2549, Stacks Tags 0F0D and 0F5Y
(blueprint: theorem-existence-exceptional-inverse-image--1).

Proof plan:
1. A finite ring is killed by a positive integer. Exact conservative coefficient forgetting,
   its bounded direct-image comparison, the pointwise proper torsion cohomology bound and
   dimension shifting prove preservation of arbitrary coproducts by the unbounded derived
   direct image (lem-sfb-finite-proper-derived-coproducts, Stacks 0F0D). Commutativity is
   unnecessary; the underlying abelian higher direct images control all coefficients.
2. Module sheaves form a Grothendieck abelian category
   (lem-sfb-arbitrary-coefficient-etale-sheaves-grothendieck). The K-injective total derived
   pushforward is triangulated (lem-pc-right-derived-functor-triangulated).
3. Apply Brown representability (lem-grothendieck-derived-brown-right-adjoint, Stacks 0F5Y).
   It supplies a right adjoint without any condition on the source or target schemes.
The separate pro-étale warning is the existing abelian-variety counterexample in
`WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts` and
`WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample`: the countable shifts of
one sheaf each lie in D⁺, while their unbounded coproduct is not preserved. -/
theorem finiteRing_isLeftAdjoint_rightDerivedLowerStar_of_isProper
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g] :
    (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.IsLeftAdjoint := by
  exact finiteRing_brown Λ g (finiteRing_preservesCoproducts_rightDerivedLowerStar Λ g)

end AlgebraicGeometry.Etale
