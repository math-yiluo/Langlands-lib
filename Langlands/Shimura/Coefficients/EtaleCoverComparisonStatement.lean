import Langlands.Shimura.Coefficients.EtaleCrossCover

/-! # Invertibility of associated-sheaf comparison between finite etale torsors -/

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry

/-- Compatible maps between finite geometric etale torsors induce isomorphisms
of the actual associated coefficient sheaves with restricted representations.
This proposition is a statement target, not a proof. -/
def EtaleAssociatedCoverComparisonStatement : Prop :=
  ∀ (X : Scheme.{u}) (G H : Type u) [Group G] [Group H]
    (Y : Action X.Etale G) (Z : Action X.Etale H),
    IsFiniteGeometricTorsor X Y → IsFiniteGeometricTorsor X Z →
    ∀ (φ : H →* G) (a : Z ⟶ (Action.res X.Etale φ).obj Y)
      (R : Type u) [CommRing R] (M : Action (ModuleCat.{u} R) G),
      IsIso (etaleCrossCoverMap X φ a
        (𝟙 ((Action.res (ModuleCat.{u} R) φ).obj M)))

end Langlands.Shimura.Coefficients
