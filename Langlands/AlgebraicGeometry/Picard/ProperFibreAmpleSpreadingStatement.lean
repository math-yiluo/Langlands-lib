import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleAffineOpenStatement

/-! # Spreading a specified fibre-ample line bundle to an affine base neighbourhood -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A specified line bundle on a proper family over a locally noetherian
base that is ample on one residue-field fibre is ample on the inverse image
of some affine open neighbourhood of that base point.
This proposition is a statement target, not a proof. -/
def ProperFibreAmpleSpreadingStatement : Prop :=
  ∀ (X S : Scheme.{u}) [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (L : LineBundle X) (s : S),
    ((LineBundle.pullback (f.fiberι s)).obj L).IsAmple →
      ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧
        ((LineBundle.pullback (f ⁻¹ᵁ V).ι).obj L).IsAmple

end Langlands.AlgebraicGeometry.Picard
