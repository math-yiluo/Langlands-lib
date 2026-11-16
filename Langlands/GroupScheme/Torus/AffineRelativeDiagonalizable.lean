import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType

/-! # Affine and relative diagonalizable models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Diagonalizable

variable (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M]

/-- The affine group-algebra model is the relative diagonalizable model
over the same affine base. -/
def relativeModelIso :
    (groupScheme R M).toGrp ≅ RelativeMultiplicativeType.diagonalizable (Spec R) M :=
  (baseChangeIso (Gm.toSpecZ (Spec R)) M).symm

/-- A finitely generated affine diagonalizable model is diagonalizable
in the arbitrary-base sense, retaining all torsion in its character group. -/
theorem isDiagonalizable_groupScheme [AddGroup.FG M] :
    RelativeMultiplicativeType.IsDiagonalizable (groupScheme R M).toGrp :=
  ⟨M, inferInstance, inferInstance, ⟨relativeModelIso R M⟩⟩

end Langlands.GroupScheme.Diagonalizable
