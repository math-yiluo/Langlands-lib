import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Embedding dimension bounds the projective dimension of the residue field -/

universe u

namespace Langlands.CommutativeAlgebra

/-- The residue field of a Noetherian local ring has projective dimension at least
the minimal number of generators of its maximal ideal (Stacks Project, Tag 00OA). -/
def ResidueFieldProjectiveDimensionLowerBoundStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
      CategoryTheory.projectiveDimension
        (ModuleCat.of R (IsLocalRing.ResidueField R))

end Langlands.CommutativeAlgebra
