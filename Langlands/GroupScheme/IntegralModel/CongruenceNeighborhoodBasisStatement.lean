import Langlands.GroupScheme.IntegralModel.CongruenceTower
import Langlands.GroupScheme.IntegralModel.LocalCompactPoints

/-! # The local-field topology target for actual integral-model congruence towers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalFieldIntegralModel

open Langlands.AlgebraicGeometry.PointTopology

/-- The actual positive-level congruence subgroups of every supplied affine finite-type
integral model are compact open, normal in its compact open integral image, and cofinal
in the full ambient identity-neighborhood filter. Smoothness is not assumed. -/
def CongruenceNeighborhoodBasisStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (M : LocalFieldIntegralModel F G),
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact (M.integralPoints : Set (rationalPoints G)) ∧
    IsOpen (M.integralPoints : Set (rationalPoints G)) ∧
    (∀ n : ℕ+,
      IsCompact (M.congruenceSubgroupAt n : Set (rationalPoints G)) ∧
      IsOpen (M.congruenceSubgroupAt n : Set (rationalPoints G)) ∧
      ((M.congruenceSubgroupAt n).subgroupOf M.integralPoints).Normal) ∧
    (∀ U : Set (rationalPoints G), U ∈ 𝓝 (1 : rationalPoints G) →
      ∃ n : ℕ+, (M.congruenceSubgroupAt n : Set (rationalPoints G)) ⊆ U)

end Langlands.GroupScheme.LocalFieldIntegralModel
