import Langlands.GroupScheme.Dynamic.AdjointDeterminant
import Langlands.GroupScheme.Dynamic.CentralizerAdjointAction
import Langlands.GroupScheme.Dynamic.SchemeDecomposition

/-! # Restriction of the adjoint determinant character from the parabolic to the Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

/-- The restriction of `det(Ad | Lie U)` from the represented parabolic `P(χ)` to the
represented centralizer `Z(χ)` (the Levi factor `M`), along the inclusion
`centralizerToParabolic`, is the determinant character of the conjugation action
`(m, u) ↦ m u m⁻¹` of `Z(χ)` on `U(χ)`, computed in the same coordinates of `Lie(U)`. -/
def AdjointDeterminantCentralizerRestrictionStatement : Prop :=
  ∀ {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
    (χ : (Gm (Spec R)).toGrp ⟶ G)
    {P Z U : GroupScheme (Spec R)} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
    (hP : (parabolic χ).IsRepresentedBy iP) (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    [IsAffineHom U.X.hom] [IsAffine P.X.left] [IsAffine Z.X.left]
    {d : ℕ} (c : Lie.FiniteCoordinates U d),
    characterRestrict (centralizerToParabolic hP hZ) (adjointDeterminantCharacter hP hU c) =
      (centralizerAdjointAction hZ hU).determinantCharacter c

end Langlands.GroupScheme.Dynamic
