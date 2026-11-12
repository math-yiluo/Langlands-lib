import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleSpreadingStatement

/-! # Fibrewise ampleness over a noetherian affine base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A specified line bundle on a proper family over a locally noetherian
affine base is ample if it is ample on every residue-field fibre. -/
def ProperAffineFibrewiseAmpleStatement : Prop :=
  ∀ (X S : Scheme.{u}) [IsAffine S] [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (L : LineBundle X),
    (∀ s : S, ((LineBundle.pullback (f.fiberι s)).obj L).IsAmple) →
      L.IsAmple

end Langlands.AlgebraicGeometry.Picard
