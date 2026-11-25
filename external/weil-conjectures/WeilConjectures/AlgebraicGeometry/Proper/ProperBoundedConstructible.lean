/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Proper direct image of bounded constructible complexes
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Proper direct image preserves ordinary bounded constructible complexes with the finite
coefficients of the smooth-base-change convention, for finite-type schemes over a field. -/
theorem isBoundedConstructible_rightDerivedLowerStar_of_proper
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (N : ℕ)
    {k : Type u} [Field k] {Y S : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (b : Y ⟶ S) [IsProper b] (hb : b ≫ aS = aY)
    (hY : IsSmoothBaseChangeCoefficients N Λ Y)
    (hS : IsSmoothBaseChangeCoefficients N Λ S)
    (K : DerivedCategoryModule Λ Y) (hK : DerivedCategory.isBoundedConstructible Λ Y K) :
    DerivedCategory.isBoundedConstructible Λ S
      ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) b).obj K) := by
  classical
  have hcompat := hb
  have hcoeffY : HasInvertibleExponent Λ Y := ⟨N, hY.1, hY.2.2.1, hY.2.2.2⟩
  by_cases hS' : IsEmpty S
  · let := hS'
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (Scheme.IsConstructibleSheaf.of_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty _)),
      0, 0, le_rfl, fun i hi ↦ Scheme.Etale.isZero_sheaf_of_isEmpty _⟩
  have : Nonempty S := not_isEmpty_iff.mp hS'
  have : HasInvertibleExponent Λ S := ⟨N, hS.1, hS.2.2.1, hS.2.2.2⟩
  have : HasInvertibleExponent Λ (Spec (.of k)) := .of_hom_of_nonempty aS
  have hK' : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K := by
    obtain ⟨hc, a, c, hac, hvan⟩ := hK
    refine ⟨⟨⟨a, ?_⟩, ⟨c, ?_⟩⟩, fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun i hi ↦ hvan i (Or.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff K c).2 fun i hi ↦ hvan i (Or.inr hi)
  obtain ⟨⟨⟨a, ha⟩, ⟨c, hc⟩⟩, hcoh⟩ :=
    boundedConstructible_rightDerivedLowerStar_of_isProper aS b hK'
  refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hcoh q),
    min a c, max a c, min_le_max, fun i hi ↦ ?_⟩
  rcases hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff _ c).1 hc i (lt_of_le_of_lt (le_max_right _ _) hi)

end AlgebraicGeometry.Etale
