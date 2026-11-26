import Langlands.AbelianScheme.PointedProjectiveAbelianLocusStatement

/-! # Representing pointed abelian-scheme structures on a smooth projective family -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry

/-- For a pointed H-projective family that is smooth of relative dimension `g`
with geometrically connected fibres over a noetherian affine base, the existence
of a pointed abelian-scheme structure is represented by a monomorphism locally
of finite presentation. -/
def PointedAbelianLawRepresentabilityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of R)) (s : Spec (CommRingCat.of R) ⟶ X) (g : ℕ),
    s ≫ p = 𝟙 _ → IsHProjective p → SmoothOfRelativeDimension g p →
    GeometricallyConnected p →
    ∃ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)),
      Mono z ∧ LocallyOfFinitePresentation z ∧
        ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)),
          (∃ f : T ⟶ Z, f ≫ z = t) ↔ HasPointedAbelianPullback p s g t

end Langlands.AbelianScheme
