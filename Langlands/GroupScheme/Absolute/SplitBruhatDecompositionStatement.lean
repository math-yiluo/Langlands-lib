import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.BruhatCellStatement
import Langlands.GroupScheme.Rational.BruhatFlagCellStatement

/-! # The split Bruhat decomposition of the group and flag quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BruhatCell

/-- A family of locally closed immersions that partitions the underlying scheme
points and the points on every field-valued test. -/
def IsImmersionPartition {S : Scheme.{u}} {I : Type u} {Y : Over S}
    {X : I → Over S} (f : (w : I) → X w ⟶ Y) : Prop :=
  (∀ w, IsImmersion (f w).left) ∧
    (∀ (K : Type u) [Field K] (a : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk a ⟶ Y),
      ∃! w, ∃ c : Over.mk a ⟶ X w, c ≫ f w = x) ∧
    ∀ x : Y.left, ∃! w, x ∈ Set.range (f w).left

end BruhatCell

/-- For a split Borel pair the actual Bruhat multiplication and flag maps
give decompositions indexed by the ground-field Weyl group. -/
def SplitBruhatDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G B : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G) (i : T.toGrp ⟶ G)
    (hG : IsConnectedReductive G), IsBorelPair b i → IsSplitTorus T.toGrp →
    letI := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    ∃ ν : cocharacterLattice T, IsRegularCocharacter i ν ∧
      let χ := CommGroupScheme.groupHom ν ≫ i
      let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
      let u := Dynamic.Affine.unipotentHom χ
      let v := Dynamic.Affine.unipotentHom χminus
      (Dynamic.parabolic χ).IsRepresentedBy b ∧
      ∃ n : relativeWeylGroup i → normalizerPoints i,
        (∀ w, (QuotientGroup.mk (n w) : relativeWeylGroup i) = w) ∧
        BruhatCell.IsImmersionPartition (fun w => BruhatCell.parametrization u v b (n w).val) ∧
        ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q)
          [Smooth q.left] [Surjective q.left] [QuasiCompact q.left],
          (∀ (X : Over (Spec (CommRingCat.of k))) (g h : X ⟶ G.X),
            g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier X) →
          BruhatCell.IsImmersionPartition (fun w => BruhatFlagCell.parametrization u v q (n w).val)

end Langlands.GroupScheme
