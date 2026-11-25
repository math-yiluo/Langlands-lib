/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Open direct images with finite allowable coefficients

Bounded constructibility is the recorded finite-stratification predicate on ordinary
etale derived categories, with no condition on Tor amplitude.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- An open immersion of finite-type schemes over a field preserves bounded constructible
complexes with arbitrary finite allowable commutative coefficients. -/
theorem isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : IsSmoothBaseChangeCoefficients N A (Spec (.of k)))
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (j : X ⟶ Y) [IsOpenImmersion j]
    (K : DerivedCategoryModule A X) (hK : DerivedCategory.isBoundedConstructible A X K) :
    DerivedCategory.isBoundedConstructible A Y
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj K) := by
  have : HasInvertibleExponent A (Spec (.of k)) := ⟨N, hA.1, hA.2.2.1, hA.2.2.2⟩
  have hK' : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
    obtain ⟨hc, a, b, _, hvan⟩ := hK
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun i hi ↦ hvan i (Or.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun i hi ↦ hvan i (Or.inr hi)
  have hpush := boundedConstructible_obj_of_forall_singleFunctor A
    (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor
    (fun F hF ↦ by
      have := hF
      exact boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_of_field A aY j F)
    hK'
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hpush
  refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
    min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
  rcases hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff _ b).1 hb i (lt_of_le_of_lt (le_max_right _ _) hi)

end AlgebraicGeometry.Etale
