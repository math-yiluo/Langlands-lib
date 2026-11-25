/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible

/-!
# Pullback preserves bounded constructibility and cohomological intervals

The coefficient categories and the essential-image predicate are the recorded
`FiniteCoefficientDerivedCategory` and `isBoundedConstructibleFiniteCoefficient`.
The auxiliary closure and preservation statements expose precisely the structures
needed to name the canonical restriction; their arguments work for every finite
commutative ring. The main statement retains the specified adic quotients `P_n`.

## References

* Stacks, Tags 09AK, 09AL and 09B5
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private theorem etaleBounded_iff (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] (L : FiniteCoefficientEtaleDerivedCategory T Λ) :
    ((∀ j : ℤ, ∃ S : Scheme.Stratification T,
      (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) ∧
      ∀ k : Fin S.n,
        ∃ d : Scheme.LocallyConstantDatum
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj
            ((_root_.DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) j).obj L)),
          ∀ i : d.cover.I₀, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
            Nonempty
              ((((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj
                ((_root_.DerivedCategory.homologyFunctor
                  (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) j).obj L)).over
                    (d.cover.etalePrecoverageToEtale i)) ≅
                (constantSheaf
                  ((S.domain k).smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
                  (ModuleCat.{u + 1} Λ)).obj M)) ∧
      ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((_root_.DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj L)) ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T L := by
  constructor
  · rintro ⟨hc, a, b, _, hab⟩
    refine ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff L a).2 (fun i hi ↦ hab i (.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff L b).2 (fun i hi ↦ hab i (.inr hi))⟩⟩, ?_⟩
    intro i
    obtain ⟨S, _, hS⟩ := hc i
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 ⟨S, hS⟩
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨?_, min a b, b, min_le_right _ _, ?_⟩
    · intro i
      obtain ⟨S, hS⟩ :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i)
      exact ⟨S, S.isConstructible_stratum, hS⟩
    · intro i hi
      rcases hi with hi | hi
      · exact (_root_.DerivedCategory.isGE_iff L a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (_root_.DerivedCategory.isLE_iff L b).1 hb i hi

private noncomputable def coefficientComparisonPullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    finiteCoefficientComparison Y Λ ⋙ finiteCoefficientPullback Y Λ f ≅
      Etale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ finiteCoefficientComparison X Λ :=
  (Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y)
    (Functor.isoWhiskerRight (finiteCoefficientRealization Y Λ).asEquivalence.unitIso.symm
      (upperStar (ModuleCat.{u + 1} Λ) f ⋙ finiteCoefficientRealization X Λ))) ≪≫
    Functor.isoWhiskerRight
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f)
      (finiteCoefficientRealization X Λ)

private noncomputable def derivedCoefficientComparisonPullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    finiteCoefficientDerivedComparison Y Λ ⋙ finiteCoefficientDerivedPullback Y Λ f ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory ⋙
        finiteCoefficientDerivedComparison X Λ :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (coefficientComparisonPullbackIso f Λ) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm


end AlgebraicGeometry.ProEtale
