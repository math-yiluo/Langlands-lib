/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootTransitions
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralLocalModels
import WeilConjectures.AlgebraicGeometry.Completed.CompletedLineDerived
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralBasis
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSingleSupport
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels

/-! # Local freeness and derived completeness of the Tate line

## References

* Stacks Project, Tag 03PK and Lemma 03RV
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

private theorem rank_one_of_cover
    {S : Scheme.{u}} {R : Sheaf (ProEt.topology S) RingCat.{u + 1}}
    (M : SheafOfModules.{u + 1} R)
    (hM : ∃ (I : Type (u + 1)) (U : I → S.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
      ∀ i, Nonempty (M.over (U i) ≅ (SheafOfModules.unit R).over (U i))) :
    M.IsFiniteLocallyFreeOfRank 1 := by
  obtain ⟨I, U, f, hc, ht⟩ := hM
  have hU : (ProEt.topology S).CoversTop U := by
    let hT : IsTerminal (ProEt.mk (𝟙 S)) := MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U f]
    exact Precoverage.generate_mem_toGrothendieck hc
  exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one M).mp
    (SheafOfModules.isInvertible_of_forall_over_unit (M := M) U hU ht)

/-- All four properties of the concrete Tate lines, including the empty-scheme case. -/
theorem pur_twist_sheaf_locally_free
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (∀ n : ℕ,
      (∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        (∀ i : I, Etale (U i).hom) ∧
        ∀ i : I, Nonempty ((purTwistRootsModule S l n).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n))).over (U i))) ∧
      (purTwistRootsModule S l n).IsFiniteLocallyFreeOfRank 1 ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Finite ((proEtaleGeometricStalk (C := AddCommGrpCat.{u + 1}) s
          (proEtaleRootsOfUnitySheaf S (l ^ (n + 1)))) : Type (u + 1))) ∧
      Epi (proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (n + 1))))) ∧
    ((∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        ∀ i : I, Nonempty ((purTwistZlModule S l).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistZlCompletion S l))).over (U i))) ∧
      (purTwistZlModule S l).IsFiniteLocallyFreeOfRank 1 ∧
      ∀ n : ℕ, Nonempty
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (purTwistZlProjection S l n)
          (purTwistZlModule S l) ≅ purTwistRootsModule S l n)) ∧
    ((∃ k : ℕ, Nonempty (@Module.Basis (Fin k) ℤ_[l]
        (Padic.coefficientExtensionIntegers l E) _ _
        (Module.compHom (Padic.coefficientExtensionIntegers l E) (purTwistIntegersMap l E)))) ∧
      IsIso (purTwistCoefficientComparison S l E) ∧
      (purTwistIntegralModule S l E).IsFiniteLocallyFreeOfRank 1 ∧
      ∀ n : ℕ,
        Nonempty (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n)
            (purTwistIntegralModule S l E) ≅ purTwistFiniteOne S l E n) ∧
        (purTwistFiniteOne S l E n).IsFiniteLocallyFreeOfRank 1 ∧
        IsLocallyConstantProEtaleModuleSheaf S (Padic.coefficientExtensionRing l E (n + 1))
          (purTwistFiniteOne S l E n) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
          Finite (proEtaleGeometricModuleStalk s
            (WeilConjectures.integralCoefficientCommRingSheaf l E S n)
            (purTwistFiniteOne S l E n))) ∧
    (∀ (D : WeilConjectures.FiniteFieldDatum.{d}) (hl : l ≠ D.p),
      (∀ n : ℕ,
        Nonempty ((WeilConjectures.integralDerivedReduction l E S D hl n).obj
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E)) ≅
            (DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ∧
        intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) S
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ∧
        proEtaleCohomologicalSupport
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ⊆ {0} ∧
        (Nonempty S → proEtaleCohomologicalSupport
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) = {0})) ∧
      WeilConjectures.IsDerivedComplete l E S D hl
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E)) ∧
      WeilConjectures.boundedConstructibleDerivedCompleteIntegral D l hl E S
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E))) := by
  classical
  obtain ⟨hfinite, hcover, hquotient⟩ := purTwistRootLocalModels S l
  have hz := rank_one_of_cover (purTwistZlModule S l) hcover
  obtain ⟨hintegral, hmodels⟩ := purTwistIntegralLocalModels S l E hz
  have hi := rank_one_of_cover (purTwistIntegralModule S l E) hintegral
  have hfmodels (n : ℕ) :
      IsLocallyConstantProEtaleModuleSheaf S (Padic.coefficientExtensionRing l E (n + 1))
        (purTwistFiniteOne S l E n) ∧
      (letI := Padic.finite_coefficientExtensionRing l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n))
       IsConstructibleProEtaleModuleSheaf S (Padic.coefficientExtensionRing l E (n + 1))
         (purTwistFiniteOne S l E n)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Finite (proEtaleGeometricModuleStalk s
          (WeilConjectures.integralCoefficientCommRingSheaf l E S n)
          (purTwistFiniteOne S l E n)) := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
    exact finiteLocallyFreeLine_models S (Padic.coefficientExtensionRing l E (n + 1))
      (purTwistFiniteOne S l E n) (rank_one_of_cover _ (hmodels n).2.1)
  have hsingle (n : ℕ) :
      intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) S
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ∧
      proEtaleCohomologicalSupport
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ⊆ {0} ∧
      (Nonempty S → proEtaleCohomologicalSupport
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) = {0}) := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
    have hc := (hfmodels n).2.1
    have hn := (hmodels n).2.2
    obtain ⟨hfin, hconst, hs, heq⟩ := constructible_single_support S
      (Padic.coefficientExtensionRing l E (n + 1)) (purTwistFiniteOne S l E n) hc _ (Iso.refl _)
    exact ⟨⟨hfin, hconst⟩, hs, fun hS ↦ heq (hn hS)⟩
  refine ⟨?_, ⟨hcover, hz, hquotient⟩, ?_, ?_⟩
  · intro n
    obtain ⟨⟨I, U, f, hc, he, ht⟩, hf⟩ := hfinite n
    exact ⟨⟨I, U, f, hc, he, ht⟩,
      rank_one_of_cover _ ⟨I, U, f, hc, ht⟩, hf, purTwistRootTransitions_epi S l n⟩
  · refine ⟨purTwistIntegralBasis l E, purTwistCoefficientComparison_isIso S l E, hi, ?_⟩
    intro n
    obtain ⟨hq, hc, _⟩ := hmodels n
    exact ⟨hq, rank_one_of_cover _ hc, (hfmodels n).1, (hfmodels n).2.2⟩
  · intro D hl
    obtain ⟨hred, hcomplete⟩ := completedLine_derived S l E (purTwistIntegralModule S l E)
      hi D hl
    have e (n : ℕ) := (hred n).some ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (hmodels n).1.some
    refine ⟨fun n ↦ ⟨⟨e n⟩, hsingle n⟩, hcomplete, hcomplete, 0, 0, le_rfl, ?_⟩
    intro n
    let := Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
    obtain ⟨hfin, hconst, hs, _⟩ := constructible_single_support S
      (Padic.coefficientExtensionRing l E (n + 1)) (purTwistFiniteOne S l E n)
      (hfmodels n).2.1 _ (e n)
    refine ⟨⟨hfin, hconst⟩, ?_⟩
    intro i hisupport
    have hi0 : i = 0 := hs hisupport
    subst i
    exact ⟨le_rfl, le_rfl⟩

end AlgebraicGeometry.Scheme
