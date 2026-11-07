import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersality

/-! # Descent of pointed Picard versality along Artinian factorizations -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation

/-- Versality descends along a chart map if all pointed Artinian maps into
the target factor through its source at the specified residue point.
The source family is identified with the actual pullback by an isomorphism. -/
def ArtinianChartVersalityDescentStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R))
    (U V : Over (Spec (CommRingCat.of R))) (i : V ⟶ U)
    (L : LineBundle ((relativeSpace f).obj U))
    (M : LineBundle ((relativeSpace f).obj V))
    (K : Type u) [Field K] [Algebra R K]
    (p : ArtinianTest.residueBase R K ⟶ V),
    Nonempty (M ≅ (LineBundle.pullback ((relativeSpace f).map i)).obj L) →
    (∀ (A : ArtinianTest R K) (a : ArtinianTest.base A ⟶ U),
      ArtinianTest.reduction A ≫ a = p ≫ i →
        ∃ b : ArtinianTest.base A ⟶ V,
          ArtinianTest.reduction A ≫ b = p ∧ b ≫ i = a) →
    PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt f M p →
      PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt f L (p ≫ i)

end Langlands.AlgebraicGeometry.Picard
