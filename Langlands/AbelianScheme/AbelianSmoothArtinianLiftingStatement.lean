import Langlands.AbelianScheme.Basic
import Mathlib.RingTheory.Artinian.Ring

/-! # Smooth proper pointed lifts of abelian schemes across elementary Artinian extensions -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- The underlying pointed scheme of an abelian scheme over the thinner ring of an elementary
extension of characteristic-zero local Artinian rings is the reduction of a smooth proper
pointed scheme over the thicker ring. -/
def AbelianSmoothArtinianLiftingStatement : Prop :=
  ∀ (R' R : Type u) [CommRing R'] [CommRing R] [IsLocalRing R'] [IsLocalRing R]
    [IsArtinianRing R'] [IsArtinianRing R] [Algebra ℚ R'] (φ : R' →+* R),
    Function.Surjective φ → IsLocalRing.maximalIdeal R' * RingHom.ker φ = ⊥ →
    ∀ B : AbelianScheme (Spec (CommRingCat.of R)),
      let t := Spec.map (CommRingCat.ofHom φ)
      ∃ (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R')) (s : Spec (CommRingCat.of R') ⟶ X),
        s ≫ p = 𝟙 _ ∧ Smooth p ∧ IsProper p ∧
        ∃ e₀ : B.X.left ≅ pullback p t,
          e₀.hom ≫ pullback.snd p t = B.X.hom ∧
            η[B.X].left ≫ e₀.hom ≫ pullback.fst p t = t ≫ s

end Langlands.AbelianScheme
