/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Constructibility tested on canonical reductions

## References

* Stacks Tags 09AL and 09C2
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale

/-- With a common cohomology interval, integral constructible completeness is equivalent
to intrinsic completeness and the cohomology clause of the uniform reduction profile. -/
theorem pbc_constructible_reduction_criterion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T] (a b : ℤ)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K))) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
      PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K ∧
        ∀ n : ℕ, DerivedCategory.homologyProperty
          (@IsConstructibleProEtaleCoefficientModuleSheaf T
            (PbcQuotient (pbcIntegralDatum l E) n) _
            ((pbcIntegralDatum l E).quotientFinite n))
          ((pbcConstantReduction T (pbcIntegralDatum l E) n).obj K) := by
  let d := pbcIntegralDatum l E
  let R (n : ℕ) := pbcRestrict (pbcLevelConstantComparison T d n).hom
  let e (n : ℕ) (q : ℤ) := ((R n).mapDerivedCategoryHomologyFunctorIso q).app
    ((pbcCompletedReduction T d n).obj K)
  constructor
  · intro h
    obtain ⟨c, e, hp⟩ := (pbcUniformReductionCriterion l E T K).mp ⟨h.2.1, h.2.2⟩
    exact ⟨h.1, fun n ↦ (hp n).2.2⟩
  · intro h
    have hprofile : PbcUniformReductionProfile T d K := by
      refine ⟨min a b, b, fun n ↦ ⟨?_, ?_, h.2 n⟩⟩
      · apply (DerivedCategory.isGE_iff _ _).mpr
        intro q hq
        exact ((R n).map_isZero
          (hbounded n q (Or.inl (lt_of_lt_of_le hq (min_le_left a b))))).of_iso (e n q).symm
      · apply (DerivedCategory.isLE_iff _ _).mpr
        intro q hq
        exact ((R n).map_isZero (hbounded n q (Or.inr hq))).of_iso (e n q).symm
    exact ⟨h.1, pbcUniformReductionCriterion_backward l E T K hprofile⟩

end AlgebraicGeometry.Scheme
