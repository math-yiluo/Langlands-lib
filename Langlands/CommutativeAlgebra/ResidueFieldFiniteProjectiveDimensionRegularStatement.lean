import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Regularity from finite projective dimension of the residue field -/

universe u

namespace Langlands.CommutativeAlgebra

/-- A Noetherian local ring whose residue field has finite projective dimension is regular.
This is implication (1) to (3) of Stacks Project Proposition 10.110.5, Tag 00OC. -/
def ResidueFieldFiniteProjectiveDimensionRegularStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    (∃ n : ℕ, CategoryTheory.HasProjectiveDimensionLE
      (ModuleCat.of R (IsLocalRing.ResidueField R)) n) →
    IsRegularLocalRing R

end Langlands.CommutativeAlgebra
