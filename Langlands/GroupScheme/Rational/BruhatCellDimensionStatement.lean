import Langlands.GroupScheme.Rational.BruhatCellStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Mathlib.Algebra.BigOperators.Finprod

/-! # The weighted relative-root dimension of a rational Bruhat factor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The unipotent factor of a rational Bruhat cell is smooth of relative
dimension equal to the sum of the multiplicities of the positive relative
roots carried to negative roots by the inverse Weyl element. -/
def RationalBruhatCellDimensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
      letI := hG.isAffineHom
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI := hi.isSplitSubtorus.mono
      IsGenericCocharacter i ν → ∀ n : normalizerPoints i,
        let χ := CommGroupScheme.groupHom ν ≫ i
        let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
        let C := BruhatCell.factor (Dynamic.Affine.unipotentHom χ)
          (Dynamic.Affine.unipotentHom χminus) n.val
        let invertedRoots := {α : characterLattice T | α ∈ relativeRoots i ∧
          0 < latticePairing T α ν ∧ latticePairing T (weylAction i n⁻¹ α) ν < 0}
        SmoothOfRelativeDimension (∑ᶠ α ∈ invertedRoots, Module.finrank k (weightSpace i α))
          C.X.hom

end Langlands.GroupScheme
