import Langlands.GroupScheme.Rational.BruhatCellStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceStatement

/-! # The unipotent factor of a rational Bruhat cell is an affine space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual unipotent intersection in a rational Bruhat cell has a split
series and is an affine space of the same smooth relative dimension. -/
def RationalBruhatCellAffineSpaceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i → ∀ ν : cocharacterLattice T,
      letI := hG.isAffineHom
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      IsGenericCocharacter i ν → ∀ n : normalizerPoints i,
        let χ := CommGroupScheme.groupHom ν ≫ i
        let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
        let U := BruhatCell.factor (Dynamic.Affine.unipotentHom χ)
          (Dynamic.Affine.unipotentHom χminus) n.val
        ∃ d : ℕ, RelativeRoot.HasSplitSeries d U ∧ SmoothOfRelativeDimension d U.X.hom ∧
          Nonempty (U.X ≅ Over.mk (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)) ↘
            Spec (CommRingCat.of k)))

end Langlands.GroupScheme
