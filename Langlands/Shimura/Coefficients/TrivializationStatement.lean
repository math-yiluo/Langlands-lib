import Langlands.Shimura.Coefficients.Etale

/-! # Exact local trivialization target for associated etale coefficient sheaves -/

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry

/-- A finite geometric etale torsor trivializes the constructed associated
sheaf after restriction to its cover, naturally in the coefficient representation.
The isomorphism is a conclusion, not additional input data. -/
def EtaleAssociatedTrivializationStatement : Prop :=
  ∀ (X : Scheme.{u}) (G : Type u) [Group G]
    (Y : Action X.Etale G), IsFiniteGeometricTorsor X Y →
    ∀ (R : Type u) [CommRing R],
      Nonempty
        ((etaleAssociatedFunctor (R := R) X Y ⋙
            (Scheme.smallEtaleTopology X).overPullback (ModuleCat.{u} R) Y.V) ≅
          (Action.forget (ModuleCat.{u} R) G ⋙
            constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R) ⋙
            (Scheme.smallEtaleTopology X).overPullback (ModuleCat.{u} R) Y.V))

end Langlands.Shimura.Coefficients
