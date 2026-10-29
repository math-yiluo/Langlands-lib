import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Local finite free representatives with minimal residue-field ranks -/

universe u

open CategoryTheory

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

attribute [local instance] HasDerivedCategory.standard

/-- Near a prime, a bounded finite projective complex admits a finite free
representative whose term ranks equal the residue-field cohomology dimensions. -/
def LocalMinimalPerfectStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ),
    IsStrictlyPerfect K →
    ∀ (p : Ideal R) [p.IsPrime],
      (∀ i : ℤ, Module.Finite p.ResidueField
        (((baseChange (algebraMap R p.ResidueField)).obj K).homology i)) ∧
      ∃ r : R, r ∉ p ∧
        ∃ P : CochainComplex (ModuleCat.{u} (Localization.Away r)) ℤ,
          IsFiniteFree P ∧
          Nonempty (DerivedCategory.Q.obj P ≅
            DerivedCategory.Q.obj
              ((baseChange (algebraMap R (Localization.Away r))).obj K)) ∧
          ∀ i : ℤ, Nonempty
            (P.X i ≃ₗ[Localization.Away r]
              (Fin (Module.finrank p.ResidueField
                (((baseChange (algebraMap R p.ResidueField)).obj K).homology i)) →
                  Localization.Away r))

end Langlands.Cohomology.ModuleComplex
