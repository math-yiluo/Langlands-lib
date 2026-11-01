import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Finite projective dimension over regular local rings -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Every finite module over a regular local ring has finite projective dimension.
This is the finite-module consequence of Stacks Project Proposition 10.110.1, Tag 00O7. -/
def RegularLocalFiniteProjectiveDimensionStatement : Prop :=
  ∀ (R : Type u) [CommRing R], IsRegularLocalRing R →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      ∃ n : ℕ, CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) n

end Langlands.CommutativeAlgebra
