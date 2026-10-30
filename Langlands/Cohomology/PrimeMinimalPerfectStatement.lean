import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Minimal finite free homotopy models at a prime -/

universe u

open CategoryTheory

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

/-- At a prime, the localization of a bounded finite projective complex is
homotopy equivalent to a finite free complex whose term ranks equal the
residue-field homology dimensions. -/
def PrimeMinimalPerfectStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ),
    IsStrictlyPerfect K →
    ∀ (p : Ideal R) [p.IsPrime],
      (∀ i : ℤ, Module.Finite p.ResidueField
        (((baseChange (algebraMap R p.ResidueField)).obj K).homology i)) ∧
      ∃ L : CochainComplex (ModuleCat.{u} (Localization.AtPrime p)) ℤ,
        IsFiniteFree L ∧
        Nonempty (HomotopyEquiv L
          ((baseChange (algebraMap R (Localization.AtPrime p))).obj K)) ∧
        ∀ i : ℤ, Nonempty
          (L.X i ≃ₗ[Localization.AtPrime p]
            (Fin (Module.finrank p.ResidueField
              (((baseChange (algebraMap R p.ResidueField)).obj K).homology i)) →
                Localization.AtPrime p))

end Langlands.Cohomology.ModuleComplex
