import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Finite residue-field projective dimension is bounded by Krull dimension -/

universe u

namespace Langlands.CommutativeAlgebra

/-- A Noetherian local ring's residue field, if it has finite projective dimension,
has projective dimension at most the ring's Krull dimension (Stacks Project, Tag 00OB). -/
def ResidueFieldProjectiveDimensionUpperBoundStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    (∃ n : ℕ, CategoryTheory.HasProjectiveDimensionLE
      (ModuleCat.of R (IsLocalRing.ResidueField R)) n) →
    CategoryTheory.projectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R)) ≤ ringKrullDim R

end Langlands.CommutativeAlgebra
