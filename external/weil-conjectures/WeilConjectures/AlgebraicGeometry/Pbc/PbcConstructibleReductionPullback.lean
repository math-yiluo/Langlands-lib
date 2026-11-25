/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import WeilConjectures.SmoothBaseChange.SbcCompletedOperations
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Canonical constructible reduction cohomology under completed pullback

## References

* Stacks Tags 099N and 09AL
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

/-- Completed pullback preserves intrinsic completeness, intrinsic reduction
constructibility, and every common cohomological support interval. -/
theorem pbc_constructible_reduction_pullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T] (g : S ⟶ T)
    (a b : ℤ) (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (_hcomplete : PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K)
    (_hconstructible : (fun K ↦ ∀ n : ℕ, DerivedCategory.homologyProperty
        (@IsConstructibleProEtaleCoefficientModuleSheaf T
          (PbcQuotient (pbcIntegralDatum l E) n) _
          ((pbcIntegralDatum l E).quotientFinite n))
        ((pbcConstantReduction T (pbcIntegralDatum l E) n).obj K)) K)
    (_hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K))) :
    PbcIsIntrinsicallyComplete S (pbcIntegralDatum l E)
        (completedPullbackObject g (pbcIntegralDatum l E) K) ∧
      (fun K ↦ ∀ n : ℕ, DerivedCategory.homologyProperty
        (@IsConstructibleProEtaleCoefficientModuleSheaf S
          (PbcQuotient (pbcIntegralDatum l E) n) _
          ((pbcIntegralDatum l E).quotientFinite n))
        ((pbcConstantReduction S (pbcIntegralDatum l E) n).obj K))
        (completedPullbackObject g (pbcIntegralDatum l E) K) ∧
      ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcCompletedReduction S (pbcIntegralDatum l E) n).obj
            (completedPullbackObject g (pbcIntegralDatum l E) K))) := by
  let d := pbcIntegralDatum l E
  let C : WeilConjectures.PbcComplete l E T := ⟨K, _hcomplete⟩
  have he (n : ℕ) : (pbcCompletedReduction S d n).obj
      (completedPullbackObject g d K) ≅
        (WeilConjectures.sbcFinitePull l E g n).obj
          ((pbcCompletedReduction T d n).obj K) := by
    let := (WeilConjectures.sbcReductionComparisons_isIso l E g n).1 C
    exact asIso (WeilConjectures.sbcPullReduction l E g n C)
  have hc (n : ℕ) (q : ℤ) := constructible_iso _ _
    (((pbcRestrict (pbcLevelConstantComparison _ d n).hom).mapDerivedCategoryHomologyFunctorIso
          q).app
        ((pbcCompletedReduction _ d n).obj K)).symm (_hconstructible n q)
  refine ⟨?_, ?_, ?_⟩
  · exact (WeilConjectures.sbcOperations_preserveComplete l E g).1 C
  · intro n q
    apply constructible_iso _ _
      (((pbcRestrict (pbcLevelConstantComparison _ d n).hom).mapDerivedCategoryHomologyFunctorIso
          q).app
          ((pbcCompletedReduction _ d n).obj _))
    let F := proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
      ((pbcAdicRings S d).obj (op n)) (asIso (completedFiniteCoefficientMap g d n))
    let L := (pbcCompletedReduction T d n).obj K
    have hc := pbc_finite_pullback_constructibility g d n
      ((DerivedCategory.homologyFunctor _ q).obj L) (hc n q)
    let eq := (F.mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
      ((DerivedCategory.homologyFunctor _ q).mapIso (he n)).symm
    exact constructible_iso S _
      ((pbcRestrict (pbcLevelConstantComparison S d n).hom).mapIso eq) hc
  · intro n q hq
    let F := proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
      ((pbcAdicRings S d).obj (op n)) (asIso (completedFiniteCoefficientMap g d n))
    exact (F.isZero_homologyFunctor_mapDerivedCategory_obj (_hbounded n q hq)).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso (he n))

end AlgebraicGeometry.Scheme
