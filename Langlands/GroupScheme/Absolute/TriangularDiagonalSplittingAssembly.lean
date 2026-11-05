import Langlands.GroupScheme.AffineNormalSubgroupQuotientEquivalence
import Langlands.GroupScheme.Absolute.TriangularDiagonalSplittingStatement
import Langlands.GroupScheme.Absolute.TriangularDiagonalImageReduction
import Langlands.GroupScheme.Absolute.TriangularActualQuotientTower
import Langlands.GroupScheme.LinearKernelTowerSection
import Langlands.GroupScheme.LinearAdditiveExtensionSplittingProof
import Langlands.GroupScheme.AffineHomImageProof
import Langlands.GroupScheme.NormalQuotientExistenceProof
import Langlands.GroupScheme.Torus.ClosedSubgroupPresentationProof

/-! # Splitting of the actual diagonal image of a triangular subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual diagonal image of an affine algebraic triangular subgroup over an
algebraically closed field admits a group-scheme section. -/
theorem triangularDiagonalSplitting : TriangularDiagonalSplittingStatement.{u} := by
  have hquot : AffineNormalSubgroupQuotientStatement.{u} :=
    normalSubgroupQuotientExistence.toAffineNormalSubgroupQuotientStatement
  intro k hk hkc H hft haff N j hj
  obtain ⟨Λ, hΛ, hΛfg, d, q, hd, hqd, hq⟩ :=
    DiagonalImageReduction.exists_triangular_diagonalizable_factorization
      affineHomImage Diagonalizable.closedSubgroupPresentation k H N j
  let : AddCommGroup Λ := hΛ
  let : AddGroup.FG Λ := hΛfg
  have ht := TriangularLayer.admitsTower_diagonalizable_of_affine_image_and_normal_quotient
    affineHomImage hquot j hj Λ d q hqd hq
  obtain ⟨s, hs⟩ :=
    LinearKernelTower.exists_section_of_admitsTower linearAdditiveExtensionSplitting ht
  exact ⟨_, d, q, s, hd, hqd, hs⟩

end Langlands.GroupScheme
