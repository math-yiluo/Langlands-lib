import Langlands.AbelianScheme.Basic
import Mathlib.RingTheory.Artinian.Ring

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- An abelian scheme lifts across an elementary extension of characteristic-zero
local Artinian rings, with an isomorphism on its actual reduction. -/
def AbelianArtinianLiftingStatement : Prop :=
  ∀ (R' R : Type u) [CommRing R'] [CommRing R] [IsLocalRing R'] [IsLocalRing R]
    [IsArtinianRing R'] [IsArtinianRing R] [Algebra ℚ R'] (φ : R' →+* R),
    Function.Surjective φ → IsLocalRing.maximalIdeal R' * RingHom.ker φ = ⊥ →
    ∀ B : AbelianScheme (Spec (.of R)),
      ∃ B' : AbelianScheme (Spec (.of R')),
        Nonempty ((AbelianScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj B' ≅ B)

end Langlands.AbelianScheme
