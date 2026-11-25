/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteConstructibility
import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteResidueTor
import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteReductionRange
import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteTowerBounds

/-! # Bounds for the finite reductions
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem packageStratumModels
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (S : Scheme.Stratification X) (i : Fin S.n)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (h : ∀ q : ℤ, HasFiniteConstantLocalModel Λ (S.domain i)
      ((CondensedRing.upperStar Λ (S.immersion i)).obj
        ((DerivedCategory.homologyFunctor _ q).obj L))) :
    finiteLocalModelsOnStratum Λ X S i L := h

private theorem expandIntegralStrata
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hs : ∀ (S : Scheme.Stratification X) (i : Fin S.n),
      integralFiniteLocalOnStratum l E X 0 S i
        ((AdicCompletion.derivedReduction l E X 0).obj K) →
      ∀ n, integralFiniteLocalOnStratum l E X n S i
        ((AdicCompletion.derivedReduction l E X n).obj K)) :
    (∀ (S : Scheme.Stratification X) (i : Fin S.n),
      (∀ q : ℤ, HasFiniteConstantLocalModel
        (DerivedNakayama.quotientRing l E 1) (S.domain i)
        ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1)
          (S.immersion i)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((AdicCompletion.derivedReduction l E X 0).obj K)))) →
      ∀ (n : ℕ) (q : ℤ),
        HasFiniteConstantLocalModel
          (DerivedNakayama.quotientRing l E (n + 1)) (S.domain i)
          ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1))
            (S.immersion i)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((AdicCompletion.derivedReduction l E X n).obj K)))) := by
  intro S i hS n q
  have hbase : integralFiniteLocalOnStratum l E X 0 S i
      ((AdicCompletion.derivedReduction l E X 0).obj K) :=
    packageStratumModels (DerivedNakayama.quotientRing l E 1) X S i
      ((AdicCompletion.derivedReduction l E X 0).obj K) hS
  exact hs S i hbase n q

/-- Bounds and constructibility for all finite reductions of a complete integral complex: if the
first reduction of `K` is bounded constructible with cohomology in `[a, b]`, then every finite
reduction is bounded constructible with Tor amplitude in `[a, b]`, `K` has cohomology in
`[a, b]`, and finite constant local models on strata propagate to all reductions. -/
theorem integral_finite_levels
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hcomplete : IsDerivedComplete l E X K)
    (h₁ : constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E 1) X
      ((AdicCompletion.derivedReduction l E X 0).obj K))
    (a b : ℤ) (hab : a ≤ b)
    (hbound : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (AdicCompletion.finiteRing l E X 0)) q).obj
        ((AdicCompletion.derivedReduction l E X 0).obj K))) :
    (∀ n : ℕ,
      constantModelBoundedConstructible
        (DerivedNakayama.quotientRing l E (n + 1)) X
        ((AdicCompletion.derivedReduction l E X n).obj K) ∧
      DerivedCategory.torAmplitudeIn
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (AdicCompletion.finiteRing l E X n)) a b
        ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
    DerivedCategory.homologyConcentratedIn
      a b K ∧
    (∀ (S : Scheme.Stratification X) (i : Fin S.n),
      (∀ q : ℤ, HasFiniteConstantLocalModel
        (DerivedNakayama.quotientRing l E 1) (S.domain i)
        ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1)
          (S.immersion i)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((AdicCompletion.derivedReduction l E X 0).obj K)))) →
      ∀ (n : ℕ) (q : ℤ),
        HasFiniteConstantLocalModel
          (DerivedNakayama.quotientRing l E (n + 1)) (S.domain i)
          ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1))
            (S.immersion i)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((AdicCompletion.derivedReduction l E X n).obj K)))) := by
  obtain ⟨hc, hs⟩ := integral_finite_constructibility l E X K h₁
  have ht (n : ℕ) := integral_finite_residue_tor l E X n
    ((AdicCompletion.derivedReduction l E X n).obj K) (hc n) a b hab (by
      obtain ⟨e⟩ := integral_finite_residue_normalization l E X K n
      intro q hq
      exact (hbound q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e))
  obtain ⟨hrange, htop⟩ := integral_finite_reduction_range l E X K a b hbound
  exact ⟨fun n ↦ ⟨hc n, ht n⟩,
    integral_finite_tower_bounds l E X K hcomplete a b hrange htop,
    expandIntegralStrata l E X K hs⟩

end AlgebraicGeometry.ProEtale
