/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Restriction to a localized ringed site preserves K-injectivity

Source: Stacks Project, Tag 08FI, Lemma 21.20.1
(blueprint: lem-pur-kinjective-restrict-localized).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Restriction of a K-injective module complex to C/U is K-injective, for any
Grothendieck topology on C.

Source: Stacks Project, Tag 08FI, Lemma 21.20.1, also used in Tag 0A94
(blueprint: lem-pur-kinjective-restrict-localized).

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
theorem isKInjective_restrict_localized
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v} R U).PreservesZeroMorphisms)
    (I : CochainComplex (SheafOfModules.{max u v} R) ℤ) [I.IsKInjective] :
    letI := hzero
    CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{max u v} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  let := hzero
  obtain ⟨G, hlimits, hcolimits, hadd, ⟨adj⟩⟩ := localized_restriction_adjunction R U hzero
  let : PreservesFiniteLimits G := hlimits
  let : PreservesFiniteColimits G := hcolimits
  let : G.IsLeftAdjoint := adj.isLeftAdjoint
  let : G.Additive := G.additive_of_preserves_binary_products
  let : (SheafOfModules.overFunctor.{max u v} R U).Additive := hadd
  let : (SheafOfModules.overFunctor.{max u v} R U).PreservesKInjectiveComplexes :=
    adj.preservesKInjectiveComplexes
  exact Functor.PreservesKInjectiveComplexes.isKInjective_map I


end CategoryTheory
