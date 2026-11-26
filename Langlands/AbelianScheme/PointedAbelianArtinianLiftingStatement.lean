import Langlands.AbelianScheme.Basic
import Mathlib.RingTheory.Artinian.Ring

/-! # Lifting a pointed abelian-scheme structure across an elementary Artinian extension -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- A smooth proper pointed family over an Artinian local ring admits an abelian-scheme
structure if its restriction across an elementary quotient admits one with the induced
identity section. -/
def PointedAbelianArtinianLiftingStatement : Prop :=
  ∀ (R B : Type u) [CommRing R] [CommRing B] [IsLocalRing R] [IsLocalRing B]
    [IsArtinianRing R] [IsArtinianRing B] (q : R →+* B),
    Function.Surjective q → IsLocalRing.maximalIdeal R * RingHom.ker q = ⊥ →
    ∀ (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R))
      (s : Spec (CommRingCat.of R) ⟶ X),
      s ≫ p = 𝟙 _ → Smooth p → IsProper p →
      let t := Spec.map (CommRingCat.ofHom q)
      (∃ (A₀ : AbelianScheme (Spec (CommRingCat.of B))) (e₀ : A₀.X.left ≅ pullback p t),
        e₀.hom ≫ pullback.snd p t = A₀.X.hom ∧
          η[A₀.X].left ≫ e₀.hom ≫ pullback.fst p t = t ≫ s) →
      ∃ (A : AbelianScheme (Spec (CommRingCat.of R))) (e : A.X.left ≅ X),
        e.hom ≫ p = A.X.hom ∧ η[A.X].left ≫ e.hom = s

end Langlands.AbelianScheme
