import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiLevi

/-! # Projecting the original parabolic compact subgroup to its Levi -/

noncomputable section

open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

universe u

variable {G : Type u} [Group G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (K : Subgroup G)

/-- The image in M of the literal intersection K in P under the original
Levi projection. -/
def projectedLeviCompact : Subgroup M := (K.subgroupOf P).map h.projection

/-- The original literal Levi intersection is contained in its projected
parabolic compact subgroup. -/
theorem subgroupOf_le_projectedLeviCompact : K.subgroupOf M ≤ projectedLeviCompact h K := by
  intro m hm
  refine ⟨Subgroup.inclusion h.levi_le m, ?_, h.projection_levi m⟩
  exact hm

/-- Projecting P in K gives a genuine Iwasawa compact factor on M from the
original G=P0 K factorization; no projection-stability of K is needed. -/
theorem isIwasawaPair_projectedLeviCompact {P0 : Subgroup G}
    (hP0 : P0 ≤ P) (hU0 : U ≤ P0) (hPK : IsIwasawaPair P0 K) :
    IsIwasawaPair (P0.subgroupOf M) (projectedLeviCompact h K) := by
  intro m
  obtain ⟨p, hp, k, hk, he⟩ := hPK (m : G)
  have hkP : k ∈ P := by
    have hke : k = p⁻¹ * m := by rw [he, inv_mul_cancel_left]
    rw [hke]
    exact P.mul_mem (P.inv_mem (hP0 hp)) (h.levi_le m.property)
  let p0 : P := Subgroup.inclusion hP0 ⟨p, hp⟩
  have hpM : (h.projection p0 : G) ∈ P0 := by
    have hu := hU0 (h.projection_inv_mul_mem p0)
    have hval : (h.projection p0 : G) = p * ((h.projection p0 : G)⁻¹ * p)⁻¹ := by group
    rw [hval]
    exact P0.mul_mem hp (P0.inv_mem hu)
  refine ⟨h.projection p0, hpM, h.projection ⟨k, hkP⟩, ⟨⟨k, hkP⟩, hk, rfl⟩, ?_⟩
  have hs : Subgroup.inclusion h.levi_le m = p0 * ⟨k, hkP⟩ := Subtype.ext he
  rw [← map_mul, ← hs]
  exact (h.projection_levi m).symm

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The projected subgroup is open because it contains the original open
literal Levi intersection. -/
theorem isOpen_projectedLeviCompact (hKo : IsOpen (K : Set G)) :
    IsOpen (projectedLeviCompact h K : Set M) :=
  Subgroup.isOpen_mono (subgroupOf_le_projectedLeviCompact h K)
    (hKo.preimage continuous_subtype_val)

omit [IsTopologicalGroup G] in
/-- The projected subgroup is compact for the displayed continuous Levi
projection and closed parabolic; it is precisely a continuous image. -/
theorem isCompact_projectedLeviCompact (hP : IsClosed (P : Set G))
    (hKc : IsCompact (K : Set G)) (hproj : Continuous h.projection) :
    IsCompact (projectedLeviCompact h K : Set M) := by
  exact (hP.isClosedEmbedding_subtypeVal.isCompact_preimage hKc).image hproj

end Langlands.HarishChandraSchwartz
