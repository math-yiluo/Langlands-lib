import Langlands.GroupScheme.Dynamic.CentralizerAdjointAction
import Langlands.GroupScheme.Lie.ActionDeterminant
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Opposite adjoint determinants on a dynamic Levi are inverse -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

/-- For a connected reductive group `G` over a field, a maximal split torus `i : T → G` and a
cocharacter `ζ` of `T`, the determinant characters of the adjoint actions of the common
centralizer `Z(ζ) = Z(-ζ)` on `Lie U(ζ)` and on `Lie U(-ζ)` add to zero in the character group
of `Z(ζ)`. The represented models of `Z(ζ)`, `U(ζ)`, `U(-ζ)` and the finite Lie coordinates are
arbitrary. This is a proof target. -/
def LeviAdjointDeterminantReciprocityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ (ζ : cocharacterLattice T)
      {Z U V : GroupScheme (Spec (CommRingCat.of k))}
      {iZ : Z ⟶ G} {iU : U ⟶ G} {iV : V ⟶ G}
      (hZ : (centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy iZ)
      (hZ' : (centralizer (CommGroupScheme.groupHom (-ζ) ≫ i)).IsRepresentedBy iZ)
      (hU : (unipotent (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy iU)
      (hV : (unipotent (CommGroupScheme.groupHom (-ζ) ≫ i)).IsRepresentedBy iV)
      [IsAffine Z.X.left] [IsAffineHom U.X.hom] [IsAffineHom V.X.hom]
      {d e : ℕ} (c : Lie.FiniteCoordinates U d) (c' : Lie.FiniteCoordinates V e),
      (centralizerAdjointAction hZ hU).determinantCharacter c +
        (centralizerAdjointAction hZ' hV).determinantCharacter c' = 0

end Langlands.GroupScheme.Dynamic
