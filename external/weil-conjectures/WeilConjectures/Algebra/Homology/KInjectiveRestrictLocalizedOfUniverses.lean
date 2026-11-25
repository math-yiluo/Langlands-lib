/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Restriction to a localized ringed site preserves K-injectivity

Source: Stacks Project, Tag 08FI, Lemma 21.20.1
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Restriction of a K-injective module complex to C/U is K-injective, for any
Grothendieck topology on C.

Source: Stacks Project, Tag 08FI, Lemma 21.20.1, also used in Tag 0A94
(auxiliary; not a blueprint node).

Proof: extension by zero sends a module presheaf N on C/U to the presheaf whose
sections at V are the direct sum of N(V,f) over arrows f : V to U, with the
R(V)-action on each summand given by restriction of R. Sheafify this presheaf.
The sectionwise adjunction, followed by the sheafification adjunction, makes this
functor left adjoint to restriction. The direct-sum functor and module
sheafification are exact; hence extension by zero is exact. Given an acyclic
complex A on C/U and a chain map A to I|U, the induced adjunction on complexes
transports it to a map from the acyclic extension of A to I. K-injectivity of I
makes that map null-homotopic. The additive adjunction transports the homotopy
back to the original chain map. This is the definition of K-injectivity of I|U.
No pullbacks, small-site hypothesis, or boundedness is required. For I = 0 this
recovers the zero homotopy, and localization at any U uses the same argument. -/
theorem isKInjective_restrict_localizedOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{max u v r}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v r} R U).PreservesZeroMorphisms)
    (I : CochainComplex (SheafOfModules.{max u v r} R) ℤ) [I.IsKInjective] :
    letI := hzero
    CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{max u v r} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  let := hzero
  obtain ⟨G, hlimits, hcolimits, hadd, ⟨adj⟩⟩ :=
    localized_restriction_adjunctionOfUniverses.{u, v, r} R U hzero
  let : PreservesFiniteLimits G := hlimits
  let : PreservesFiniteColimits G := hcolimits
  let : G.IsLeftAdjoint := adj.isLeftAdjoint
  let : G.Additive := G.additive_of_preserves_binary_products
  let : (SheafOfModules.overFunctor.{max u v r} R U).Additive := hadd
  let : (SheafOfModules.overFunctor.{max u v r} R U).PreservesKInjectiveComplexes :=
    adj.preservesKInjectiveComplexes
  exact Functor.PreservesKInjectiveComplexes.isKInjective_map I

end CategoryTheory
