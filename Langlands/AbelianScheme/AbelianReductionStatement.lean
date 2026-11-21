import Langlands.AbelianScheme.NeronModel
import Langlands.GroupScheme.RelativeIdentityComponent

/-! # Abelian reduction of a supplied Néron model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.GroupScheme

namespace Langlands.AbelianScheme

/-- A Néron model of an abelian variety with proper geometric special identity
component is proper with geometrically connected fibres. -/
def AbelianReductionStatement : Prop :=
  ∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (B : AbelianScheme (Spec (CommRingCat.of K)))
    (N : NeronModel V K B)
    (J : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField V)))))
    (i : J ⟶ N.geometricSpecialFibre),
    IsRelativeIdentityComponent N.geometricSpecialFibre.toGrp (CommGroupScheme.groupHom i) →
      IsProper J.X.hom → IsProper N.group.X.hom ∧ GeometricallyConnected N.group.X.hom

end Langlands.AbelianScheme
