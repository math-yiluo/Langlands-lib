import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Descent of a finite free homotopy model from a prime localization -/

universe u

open CategoryTheory

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

/-- A finite free homotopy model of a bounded finite projective complex over
`R_p`, with prescribed term ranks, descends to one finite free homotopy model
with the same ranks over a single localization `R_r` with `r ∉ p`. -/
def PrimeFreeHomotopyDescentStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ),
    IsStrictlyPerfect K →
    ∀ (p : Ideal R) [p.IsPrime] (n : ℤ → ℕ)
      (L : CochainComplex (ModuleCat.{u} (Localization.AtPrime p)) ℤ),
      IsFiniteFree L →
      Nonempty (HomotopyEquiv L
        ((baseChange (algebraMap R (Localization.AtPrime p))).obj K)) →
      (∀ i : ℤ, Nonempty (L.X i ≃ₗ[Localization.AtPrime p]
        (Fin (n i) → Localization.AtPrime p))) →
      ∃ r : R, r ∉ p ∧
        ∃ P : CochainComplex (ModuleCat.{u} (Localization.Away r)) ℤ,
          IsFiniteFree P ∧
          Nonempty (HomotopyEquiv P
            ((baseChange (algebraMap R (Localization.Away r))).obj K)) ∧
          ∀ i : ℤ, Nonempty (P.X i ≃ₗ[Localization.Away r]
            (Fin (n i) → Localization.Away r))

end Langlands.Cohomology.ModuleComplex
