import Langlands.GroupScheme.Dynamic.SplitContractingSubgroup
import Langlands.GroupScheme.Reductive.SplitNormalFactorProduct
import Langlands.GroupScheme.SubgroupFunctor.FppfProductNormalization
import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # A normal split product inside a supplied pseudo-parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace PseudoParabolicSplitNormalProduct

variable {k : Type u} [Field k]
    {G P V W : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual split smooth connected normal subgroup of `P` representing
`U_G(χ) R_us(G)` inside `G`. -/
structure NormalProduct
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (n : V ⟶ G) (i : P ⟶ G) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ P
  isClosedSubgroup : IsClosedSubgroup inclusion
  isFppfProduct : SubgroupFunctor.IsFppfProduct
    (Dynamic.unipotent χ) (SubgroupFunctor.range n) (inclusion ≫ i)
  smooth : Smooth group.X.hom
  connectedSpace : ConnectedSpace group.X.left
  isUnipotent : IsUnipotent group
  isSplitUnipotent : RelativeRoot.IsSplitUnipotent group
  isNormal : (SubgroupFunctor.range inclusion).IsNormal

variable [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- The split-product presentation of `P` makes the actual product
`U_G(χ) R_us(G)` normal in `P`. -/
def normalProduct
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (n : V ⟶ G) (i : P ⟶ G)
    (hP : (Dynamic.parabolic χ).IsFppfProduct (SubgroupFunctor.range n) i)
    (hn : IsSplitUnipotentRadical n) : NormalProduct χ n i := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let U := Dynamic.Affine.unipotentScheme χ
  let j : U ⟶ G := Dynamic.Affine.unipotentHom χ
  have hj : (Dynamic.unipotent χ).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hjc : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  let : Smooth U.X.hom := (dynamicSmooth k G χ U j).2.2 hj
  let : ConnectedSpace U.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χ hj
  let : Smooth V.X.hom := hn.smooth
  let : ConnectedSpace V.X.left := hn.connectedSpace
  let D := SplitNormalFactorProduct.product j n hjc hn.isClosedSubgroup hn.isNormal
    (Dynamic.isSplitUnipotent_of_isRepresentedBy_unipotent χ hj hjc) hn.isSplitUnipotent
  have hd : (Dynamic.unipotent χ).IsFppfProduct (SubgroupFunctor.range n) D.inclusion := by
    simpa only [hj.2] using D.isFppfProduct
  let : IsClosedImmersion i.hom.hom.left := hP.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hDi : SubgroupFunctor.range D.inclusion ≤ SubgroupFunctor.range i :=
    hd.le_range i (le_trans (Dynamic.unipotent_le_parabolic χ) hP.left_le) hP.right_le
  let hrep : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let q : D.group ⟶ P := hrep.factorHom D.inclusion hDi
  have hq : q ≫ i = D.inclusion := hrep.factorHom_comp D.inclusion hDi
  have hDP : (SubgroupFunctor.range D.inclusion).IsNormalizedBy (Dynamic.parabolic χ) :=
    hd.isNormalizedBy (Dynamic.unipotent_isNormalizedBy_parabolic χ)
      (fun T g x _ hx => hn.isNormal T g x (Subgroup.mem_top _) hx)
  have hDN : (SubgroupFunctor.range D.inclusion).IsNormalizedBy (SubgroupFunctor.range n) :=
    SubgroupFunctor.isNormalizedBy_of_le hd.right_le
  have hnormal : (SubgroupFunctor.range q).IsNormal := by
    apply SubgroupFunctor.isNormal_range_of_isNormalizedBy_comp q i
    rw [hq]
    exact hP.normalizes hd.isFppfLocal hDP hDN
  exact
    { group := D.group
      inclusion := q
      isClosedSubgroup := IsClosedSubgroup.of_comp hP.isClosedSubgroup
        (by rw [hq]; exact hd.isClosedSubgroup)
      isFppfProduct := by rw [hq]; exact hd
      smooth := D.smooth
      connectedSpace := D.connectedSpace
      isUnipotent := D.isUnipotent
      isSplitUnipotent := D.isSplitUnipotent
      isNormal := hnormal }

/-- Maximality of the supplied split radical of `P` contains both factors
of the constructed split normal product on every relative scheme test. -/
theorem containment
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (n : V ⟶ G) (i : P ⟶ G)
    (hP : (Dynamic.parabolic χ).IsFppfProduct (SubgroupFunctor.range n) i)
    (hn : IsSplitUnipotentRadical n) (m : W ⟶ P) (hm : IsSplitUnipotentRadical m) :
    Dynamic.unipotent χ ≤ SubgroupFunctor.range (m ≫ i) ∧
      SubgroupFunctor.range n ≤ SubgroupFunctor.range (m ≫ i) := by
  let D := normalProduct χ n i hP hn
  have hD := hm.greatest D.group D.inclusion D.isClosedSubgroup D.smooth
    D.connectedSpace D.isUnipotent D.isSplitUnipotent D.isNormal
  have hcomp : SubgroupFunctor.range (D.inclusion ≫ i) ≤ SubgroupFunctor.range (m ≫ i) := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy : y ≫ D.inclusion.hom.hom ∈ (SubgroupFunctor.range D.inclusion).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp (hD T hy)
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨z, ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun a => a ≫ i.hom.hom) hz
  exact ⟨le_trans D.isFppfProduct.left_le hcomp, le_trans D.isFppfProduct.right_le hcomp⟩

end PseudoParabolicSplitNormalProduct

end Langlands.GroupScheme
