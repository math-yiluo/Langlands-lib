import Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement
import Langlands.BruhatTits.RationalPoints.CentralNormKernel.Bound
import Langlands.BruhatTits.RationalPoints.CentralNormKernel.BoundedCompact
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.Representation.Plancherel.RationalCharacterTopology

/-! # Compactness of the full scheme-centre intersection with the rational norm kernel

Proof of `CentralNormKernelCompactnessStatement`. A closed linear embedding `ρ` of the connected
reductive group `M` identifies rational points with a closed set of invertible matrices. The
scheme-centre points and the rational common norm kernel are closed, and the matrix entries of
their common points, and of the inverses of these points, are bounded
(`CentralNormKernel.exists_entry_bound`). A closed set of rational points with bounded matrix
entries is compact (`CentralNormKernel.isCompact_of_isClosed_of_bounded`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.RationalPoints

/-- **Compactness of the central norm kernel.** For every nonarchimedean local field `F` and
connected reductive group `M` over `F`, the intersection of the full scheme-centre points with
the rational common norm kernel is compact in the canonical rational-point topology. -/
theorem centralNormKernelCompactness : CentralNormKernelCompactnessStatement.{u} := by
  intro F _ _ _ _ M hM
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
  change IsCompact ((GroupScheme.schemeCenterPoints M ⊓
    Plancherel.rationalCommonNormKernel M : Subgroup (GroupScheme.rationalPoints M)) :
      Set (GroupScheme.rationalPoints M))
  have : Smooth M.X.hom := hM.smooth
  have : LocallyOfFiniteType M.X.hom := inferInstance
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement F M hM.isAffineHom inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  obtain ⟨C, hC⟩ :=
    CentralNormKernel.exists_entry_bound hM.hasTrivialGeometricUnipotentRadical ρ
  have : T2Space F := by
    let := LocalGalois.localNormedField F
    exact inferInstance
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence_of_isAffineHom hM.isAffineHom
  have hZ : IsClosed (GroupScheme.schemeCenterPoints M : Set (GroupScheme.rationalPoints M)) :=
    isClosed_rationalPoint_subgroup F (center M) z hz.isRepresentedBy hz.1
  have hK : IsClosed
      (Plancherel.rationalCommonNormKernel M : Set (GroupScheme.rationalPoints M)) :=
    Plancherel.isClosed_rationalCommonNormKernel M
  rw [Subgroup.coe_inf]
  refine CentralNormKernel.isCompact_of_isClosed_of_bounded ρ _ (hZ.inter hK) C ?_
  intro g hg k l
  have hg' : g ∈ GroupScheme.schemeCenterPoints M ⊓ Plancherel.rationalCommonNormKernel M :=
    Subgroup.mem_inf.2 hg
  refine ⟨hC g hg' k l, ?_⟩
  have h := hC g⁻¹ (inv_mem hg') k l
  rwa [map_inv] at h

end Langlands.BruhatTits.RationalPoints
