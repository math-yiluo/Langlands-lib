import Langlands.GroupScheme.HomScheme.GeneralLinearTorusModuliAffineSumStatement
import Langlands.GroupScheme.Torus.OrderedProjectorAffineSum

/-! # The affine open decomposition of the moduli of subtori of `GL_n` -/

universe u

namespace Langlands.GroupScheme.TorusSubgroupModuli

/-- The moduli of closed relative subtori of a general linear group over an affine base
is the union of pairwise disjoint affine opens. -/
theorem generalLinearAffineSum : GeneralLinearAffineSumStatement.{u} := by
  intro R n _ _ M K j hj hK hu
  exact OrderedProjectorScheme.exists_disjoint_affineOpen_cover j hj hK hu

end Langlands.GroupScheme.TorusSubgroupModuli
