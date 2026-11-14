import Langlands.GroupScheme.Absolute.TriangularDiagonalKernelTowerStatement
import Langlands.GroupScheme.Absolute.TriangularActualQuotientTower
import Langlands.GroupScheme.AffineHomImageProof
import Langlands.GroupScheme.AffineNormalSubgroupQuotientProof

/-! # Character-linear towers for the supplied triangular diagonal image -/

universe u

namespace Langlands.GroupScheme

/-- The supplied actual diagonal quotient has a finite character-linear tower
in every universe and over every field. -/
theorem triangularDiagonalKernelTower : TriangularDiagonalKernelTowerStatement.{u} := by
  intro k hk H hft haff N j hj
  dsimp only
  intro Λ hΛ hΛfg q d hd hfac hq
  exact TriangularLayer.admitsTower_diagonalizable_of_affine_image_and_normal_quotient
    affineHomImage affineNormalSubgroupQuotient j hj Λ d q hfac hq

end Langlands.GroupScheme
