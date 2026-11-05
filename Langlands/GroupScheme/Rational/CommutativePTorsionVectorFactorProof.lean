import Langlands.GroupScheme.Rational.CommutativePTorsionVectorFactorStatement
import Langlands.GroupScheme.Rational.SmoothCommutativePTorsionVectorEmbeddingProof
import Langlands.GroupScheme.Rational.ClosedVectorSubgroupFactor
import Langlands.GroupScheme.CommutativeSplitProduct
import Langlands.GroupScheme.Rational.CommutativePTorsionGeometry

/-! # A vector factor with a separably wound complement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

/-- The exact ground-field vector-factor assertion, with the full smooth
connected unipotent kernel constant on affine lines after separable closure. -/
theorem commutativePTorsionVectorFactor :
    CommutativePTorsionVectorFactorStatement.{u} := by
  intro k _ p _ _ U hSmooth hAffine hConnected hU
  have := hSmooth
  have := hAffine
  have := hConnected
  obtain ⟨V, i, hi, n, hV⟩ :=
    smoothCommutativePTorsionVectorEmbedding k p U hSmooth hAffine hU
  let e := hV.iso
  let j := i ≫ e.hom
  have hj : IsClosedSubgroup j := by
    let : IsClosedImmersion i.hom.hom.left := hi
    have : IsIso e.hom.hom.hom.left :=
      (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map e.hom))
    change IsClosedImmersion (i.hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  let d := ClosedVectorSubgroup.separableLineRetraction n U.toGrp j hj
  let V' := VectorGroup.groupScheme (CommRingCat.of k) d.dimension
  let q := d.retraction
  let s := d.sectionMap
  have hs : s ≫ q = 𝟙 V' := d.section_comp_retraction
  have hv : IsVectorGroupOfDimension V' d.dimension :=
    ⟨VectorGroup.coordinates (CommRingCat.of k) d.dimension,
      VectorGroup.isNaturalVectorCoordinates⟩
  have : IsAffineHom V'.X.hom := hv.isAffineHom
  let W := CommutativeSplitProduct.complement q
  have hgeometry := CommutativeSplitProduct.complement_geometry q s hs
  have : Smooth W.X.hom := hgeometry.1
  have : IsAffineHom W.X.hom := hgeometry.2.1
  have : ConnectedSpace W.X.left := hgeometry.2.2
  have hWexp : HasUniformPowerExponent W.toGrp p := hU.of_mono (kernelι q)
  have hWunipotent : IsUnipotent W.toGrp :=
    CommutativePTorsion.isUnipotent p W hWexp
  let b := algebraBaseMap k (SeparableClosure k)
  let F := GroupScheme.baseChange b
  have hsb : F.map s ≫ F.map q = 𝟙 _ := by
    rw [← F.map_comp, hs, F.map_id]
  have hconstKernel : HasConstantAffineLineMaps (kernel (F.map q)) :=
    CapturesPointedAffineLineMaps.kernel_hasConstantAffineLineMaps
      (F.map q) (F.map s) hsb d.captures
  have hconst : HasConstantAffineLineMaps (F.obj W.toGrp) :=
    hconstKernel.of_mono (kernelBaseChangeIso b q).hom.hom.hom
  exact ⟨V', W, ⟨CommutativeSplitProduct.factorIso q s hs⟩,
    ⟨d.dimension, hv⟩, hgeometry.1, hgeometry.2.1, hgeometry.2.2,
    hWunipotent, hconst⟩

end Langlands.GroupScheme.RelativeRoot
