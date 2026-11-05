import Langlands.GroupScheme.IntegralModel.LocalField
import Langlands.GroupScheme.IntegralModel.CompactPoints

/-! # Compactness of the actual local-field integral-point image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  (M : IntegralModel ↥𝒪[F] F G)

private instance modelAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

private instance localFieldHausdorff : T2Space F := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

local instance localFieldSectionTopology : TopologicalSpace M.integralSections :=
  rationalPointTopology ↥𝒪[F] M.group.X

local instance localFieldGenericTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- The original integral-point map for the canonical valuation integer ring,
bundled continuously for the existing evaluation topologies. -/
def localFieldIntegralPointContinuousHom :
    M.integralSections →ₜ* rationalPoints G :=
  M.integralPointContinuousHom continuous_subtype_val

@[simp] theorem localFieldIntegralPointContinuousHom_apply (x : M.integralSections) :
    M.localFieldIntegralPointContinuousHom x = M.integralPointMap x := rfl

/-- Compactness of the actual supplied-model image over the canonical integers. -/
theorem isCompact_integralPoints_localField :
    IsCompact (M.integralPoints : Set (rationalPoints G)) :=
  M.isCompact_integralPoints continuous_subtype_val

end Langlands.GroupScheme.IntegralModel
