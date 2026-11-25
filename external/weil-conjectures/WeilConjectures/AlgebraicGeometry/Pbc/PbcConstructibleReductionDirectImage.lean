/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Pbc.PbcFiniteDirectImageCohomology
import WeilConjectures.SmoothBaseChange.SbcCompletedOperations
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Divisibility.Units
import Mathlib.GroupTheory.OrderOfElement

set_option linter.privateModule false

/-! # Canonical constructible reduction cohomology under proper direct image

## References

* Stacks Tags 095U and 0GL0
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale

private theorem lisse_iso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A]
    {F G : pbcModules Y ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (adicLisseConstantRing X A))} (e : F ≅ G)
    (h : IsRelativelyFiniteLisseModule g A F) : IsRelativelyFiniteLisseModule g A G := by
  obtain ⟨S, hS, hs⟩ := h
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨M, hM, ⟨eM⟩⟩ := hs V f hf
  exact ⟨M, hM, ⟨((SheafOfModules.overFunctor _ V).mapIso e).symm ≪≫ eM⟩⟩

private theorem constructible_iso (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {F G : pbcModules T (adicLisseConstantRing T A)} (e : F ≅ G)
    (h : IsConstructibleProEtaleCoefficientModuleSheaf T A F) :
    IsConstructibleProEtaleCoefficientModuleSheaf T A G := by
  obtain ⟨S, hSn, hSc, hS⟩ := h
  refine ⟨S, hSn, hSc, ?_⟩
  intro i
  exact lisse_iso (S.immersion i) A
    ((proEtaleModuleInverseImage (S.immersion i) (adicLisseConstantRing T A)).mapIso e) (hS i)

end AlgebraicGeometry.Scheme
