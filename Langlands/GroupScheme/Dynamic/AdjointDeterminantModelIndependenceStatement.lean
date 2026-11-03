import Langlands.GroupScheme.Dynamic.AdjointDeterminant
import Langlands.GroupScheme.Dynamic.CentralizerAdjointAction
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Independence of the adjoint determinant character from the represented models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

open SubgroupFunctor.IsRepresentedBy

/-- The adjoint determinant characters `det(Ad | Lie U)` on the parabolic `P(χ)` and on the
centralizer `Z(χ)` do not depend on the chosen representing group schemes of `P(χ)`, `Z(χ)`,
`U(χ)` or on the chosen finite coordinates of `Lie(U)`: they correspond under restriction along
the canonical isomorphism between two representing models. -/
def AdjointDeterminantModelIndependenceStatement : Prop :=
  ∀ {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} (χ : (Gm (Spec R)).toGrp ⟶ G)
    {U U' : GroupScheme (Spec R)} {iU : U ⟶ G} {iU' : U' ⟶ G}
    (hU : (unipotent χ).IsRepresentedBy iU) (hU' : (unipotent χ).IsRepresentedBy iU')
    [IsAffineHom U.X.hom] [IsAffineHom U'.X.hom]
    {d d' : ℕ} (c : Lie.FiniteCoordinates U d) (c' : Lie.FiniteCoordinates U' d'),
    (∀ {P P' : GroupScheme (Spec R)} {iP : P ⟶ G} {iP' : P' ⟶ G}
      (hP : (parabolic χ).IsRepresentedBy iP) (hP' : (parabolic χ).IsRepresentedBy iP')
      [IsAffine P.X.left] [IsAffine P'.X.left],
      characterRestrict (isoOfIsRepresentedBy hP hP').hom
          (adjointDeterminantCharacter hP' hU' c') =
        adjointDeterminantCharacter hP hU c) ∧
    (∀ {Z Z' : GroupScheme (Spec R)} {iZ : Z ⟶ G} {iZ' : Z' ⟶ G}
      (hZ : (centralizer χ).IsRepresentedBy iZ) (hZ' : (centralizer χ).IsRepresentedBy iZ')
      [IsAffine Z.X.left] [IsAffine Z'.X.left],
      characterRestrict (isoOfIsRepresentedBy hZ hZ').hom
          ((centralizerAdjointAction hZ' hU').determinantCharacter c') =
        (centralizerAdjointAction hZ hU).determinantCharacter c)

end Langlands.GroupScheme.Dynamic
