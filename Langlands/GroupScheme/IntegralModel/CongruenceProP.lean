import Langlands.GroupScheme.IntegralModel.CongruencePowers
import Langlands.GroupScheme.IntegralModel.CongruenceNeighborhoodBasisProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPointEvaluation
import Langlands.Cohomology.DivisibleSystem.ProPInvariants

/-! # The actual local-field congruence subgroups are pro-p -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.AlgebraicGeometry.PointTopology Langlands.Cohomology

namespace Langlands.GroupScheme.IntegralModel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  (M : IntegralModel ↥𝒪[F] F G)

local instance congruenceProPPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance congruenceProPPointTotallyDisconnected :
    TotallyDisconnectedSpace (rationalPoints G) :=
  rationalPoint_totallyDisconnectedSpace_of_localField F G.X

/-- The actual positive-level congruence subgroup, bundled with its openness
in the original generic rational-point topology. -/
def localFieldCongruenceOpenSubgroup (n : ℕ+) : OpenSubgroup (rationalPoints G) :=
  ⟨M.congruenceSubgroupAt n,
    ((LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof F G M).2.2.1 n).2.1⟩

@[simp] theorem localFieldCongruenceOpenSubgroup_toSubgroup (n : ℕ+) :
    (M.localFieldCongruenceOpenSubgroup n).toSubgroup = M.congruenceSubgroupAt n := rfl

/-- Every open normal quotient of an actual positive congruence subgroup is
a group in which every element is killed by a power of the residue characteristic. -/
theorem localField_isPGroup_congruenceQuotient (n : ℕ+)
    (N : OpenNormalSubgroup (M.congruenceSubgroupAt n)) :
    IsPGroup (ringChar 𝓀[F]) ((M.congruenceSubgroupAt n) ⧸ N.toSubgroup) := by
  have hb := LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof F G M
  let U : Set (rationalPoints G) :=
    Subtype.val '' (N : Set (M.congruenceSubgroupAt n))
  have hU : IsOpen U :=
    (hb.2.2.1 n).2.1.isOpenMap_subtype_val _ N.isOpen
  have h1U : (1 : rationalPoints G) ∈ U := ⟨1, N.one_mem, rfl⟩
  obtain ⟨k, hk⟩ := hb.2.2.2 U (hU.mem_nhds h1U)
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  refine ⟨(k : ℕ), ?_⟩
  apply (QuotientGroup.eq_one_iff _).mpr
  change x ^ (ringChar 𝓀[F] ^ (k : ℕ)) ∈ N.toSubgroup
  have hx := M.pow_pow_mem_congruenceSubgroupAt n (ringChar 𝓀[F])
    (residueChar_mem_maximalIdeal (R := ↥𝒪[F])) x.property (k : ℕ)
  have hkn : k ≤ (⟨(n : ℕ) + (k : ℕ), Nat.add_pos_left n.pos (k : ℕ)⟩ : ℕ+) := by
    change (k : ℕ) ≤ (n : ℕ) + (k : ℕ)
    omega
  have hxk := hk (M.congruenceSubgroupAt_antitone hkn hx)
  obtain ⟨y, hy, hyx⟩ := hxk
  have hxy : y = x ^ (ringChar 𝓀[F] ^ (k : ℕ)) := Subtype.ext hyx
  exact hxy ▸ hy

/-- Every positive congruence subgroup of the original model is pro-p for the
actual residue characteristic, in its induced rational-point topology. -/
theorem localField_isProP_congruenceSubgroupAt (n : ℕ+) :
    IsProPSubgroup (ringChar 𝓀[F]) (M.congruenceSubgroupAt n) where
  prime := CharP.prime_ringChar 𝓀[F]
  compactSpace := isCompact_iff_compactSpace.mp
    (((LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof F G M).2.2.1 n).1)
  totallyDisconnectedSpace := inferInstance
  isPGroup := M.localField_isPGroup_congruenceQuotient n

/-- The published level-one congruence subgroup is pro-p. -/
theorem localField_isProP_congruenceSubgroup :
    IsProPSubgroup (ringChar 𝓀[F]) M.congruenceSubgroup := by
  simpa only [congruenceSubgroupAt_one] using M.localField_isProP_congruenceSubgroupAt 1

end Langlands.GroupScheme.IntegralModel
