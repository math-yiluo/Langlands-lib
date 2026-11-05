import Langlands.GroupScheme.Reductive.SplitNormalFppfProductProof
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalFactorProduct
import Langlands.GroupScheme.Rational.SplitSeriesUnipotent

/-! # Split products with a normal right factor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SplitNormalFactorProduct

variable {k : Type u} [Field k]
    {G H N D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [Smooth N.X.hom] [ConnectedSpace N.X.left]

/-- Splitness of a represented product needs only the right factor to be
normal in the ambient group. -/
theorem isSplitUnipotent (i : H ⟶ G) (j : N ⟶ G) (d : D ⟶ G)
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hn : (SubgroupFunctor.range j).IsNormal)
    (hH : RelativeRoot.IsSplitUnipotent H)
    (hN : RelativeRoot.IsSplitUnipotent N)
    (hd : SubgroupFunctor.IsFppfProduct
      (SubgroupFunctor.range i) (SubgroupFunctor.range j) d)
    [Smooth D.X.hom] : RelativeRoot.IsSplitUnipotent D := by
  let : IsClosedImmersion d.hom.hom.left := hd.isClosedSubgroup
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  let hrep : (SubgroupFunctor.range d).IsRepresentedBy d := ⟨inferInstance, rfl⟩
  let i' : H ⟶ D := hrep.factorHom i hd.left_le
  let j' : N ⟶ D := hrep.factorHom j hd.right_le
  have hi' : i' ≫ d = i := hrep.factorHom_comp i hd.left_le
  have hj' : j' ≫ d = j := hrep.factorHom_comp j hd.right_le
  have hjc : IsClosedSubgroup j' :=
    IsClosedSubgroup.of_comp hd.isClosedSubgroup (by rw [hj']; exact hj)
  have hnj : (SubgroupFunctor.range j').IsNormal :=
    SubgroupFunctor.isNormal_range_of_mono_comp j' d (by rw [hj']; exact hn)
  let : IsAffineHom H.X.hom := hi.isAffineHom
  let : IsAffineHom D.X.hom := hd.isClosedSubgroup.isAffineHom
  obtain ⟨n, hseries⟩ := hH
  exact RelativeRoot.SplitSemidirect.isSplitUnipotent_of_surjective
    (SplitNormalFppfProduct.homImageHypothesis k) n j' i' hjc hnj hN hseries
    (SplitNormalFppfProduct.surjective_mulPoints hd i' j' hi' hj' hnj)

/-- Actual data for a smooth connected split-unipotent represented product. -/
structure Product (i : H ⟶ G) (j : N ⟶ G) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ G
  isFppfProduct : SubgroupFunctor.IsFppfProduct
    (SubgroupFunctor.range i) (SubgroupFunctor.range j) inclusion
  smooth : Smooth group.X.hom
  connectedSpace : ConnectedSpace group.X.left
  isUnipotent : IsUnipotent group
  isSplitUnipotent : RelativeRoot.IsSplitUnipotent group

variable [LocallyOfFiniteType G.X.hom]

/-- Construct the split-unipotent product by the smooth connected image
construction and the finite split-series criterion. -/
def product (i : H ⟶ G) (j : N ⟶ G)
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hn : (SubgroupFunctor.range j).IsNormal)
    (hH : RelativeRoot.IsSplitUnipotent H)
    (hN : RelativeRoot.IsSplitUnipotent N) : Product i j := by
  let ex :=
    SmoothConnectedNormalFactorProduct.exists_isFppfProduct i j hi hj hn
  let D := ex.choose
  let d := ex.choose_spec.choose
  have hd := ex.choose_spec.choose_spec.1
  have hDs := ex.choose_spec.choose_spec.2.1
  have hDc := ex.choose_spec.choose_spec.2.2
  let : Smooth D.X.hom := hDs
  let : IsAffineHom D.X.hom := hd.isClosedSubgroup.isAffineHom
  have hsplit := isSplitUnipotent i j d hi hj hn hH hN hd
  exact ⟨D, d, hd, hDs, hDc, hsplit.isUnipotent, hsplit⟩

end SplitNormalFactorProduct

end Langlands.GroupScheme
