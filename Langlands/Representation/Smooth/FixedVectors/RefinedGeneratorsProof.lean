import Langlands.Representation.Smooth.FixedVectors.RefinedGeneratorsStatement
import Langlands.Representation.Smooth.FixedVectors.LengthCriterionProof
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-! Normal compact-open and supplied-basis refinements of common fixed generators. -/

set_option autoImplicit false

noncomputable section

open Topology

namespace Langlands

universe uR uG uV

/-- Refine common smooth generators inside a prescribed compact open subgroup,
retaining normality in that same subgroup and any prescribed smallness. -/
theorem commonCompactOpenNormalGenerators :
    CommonCompactOpenNormalGeneratorsStatement.{uR, uG, uV} := by
  intro R _ G _ _ _ V _ _ ρ hρ hfin K₀ hK₀ U hU
  obtain ⟨n, v, F, hgen, hfix, hgenerate⟩ :=
    commonFixedGenerators R G V ρ hρ hfin
  obtain ⟨J, hJ⟩ := NonarchimedeanGroup.is_nonarchimedean U hU
  let : IsTopologicalGroup K₀ := inferInstanceAs (IsTopologicalGroup K₀.toSubgroup)
  let H : OpenSubgroup K₀ :=
    (F ⊓ J).comap K₀.toSubgroup.subtype continuous_subtype_val
  let : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK₀
  obtain ⟨N, hN⟩ :=
    IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      H.isClopen H.one_mem
  let K : OpenSubgroup G :=
    { toSubgroup := N.toSubgroup.map K₀.toSubgroup.subtype
      isOpen' := K₀.isOpen.isOpenMap_subtype_val _ N.toOpenSubgroup.isOpen }
  have hKK₀ : K ≤ K₀ := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hKF : K ≤ F := by
    rintro x ⟨y, hy, rfl⟩
    exact (hN hy).1
  have hKU : (K : Set G) ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact hJ (hN hy).2
  have hnormal : (K.toSubgroup.subgroupOf K₀.toSubgroup).Normal := by
    change ((N.toSubgroup.map K₀.toSubgroup.subtype).comap
      K₀.toSubgroup.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective K₀.toSubgroup.subtype_injective]
    infer_instance
  refine ⟨n, v, K, hK₀.of_isClosed_subset K.isClosed hKK₀, hKK₀,
    hnormal, hKU, hgen, ?_, ?_⟩
  · intro i g
    exact hfix i ⟨g, hKF g.property⟩
  · intro L hL S hS
    exact hgenerate L (hL.trans hKF) S hS

/-- Select a member of the supplied subgroup neighborhood basis inside the
prescribed neighborhood and the common open stabilizer. -/
theorem commonBasisFixedGenerators :
    CommonBasisFixedGeneratorsStatement.{uR, uG, uV} := by
  intro R _ G _ _ V _ _ ρ hρ hfin B hB U hU
  obtain ⟨n, v, F, hgen, hfix, hgenerate⟩ :=
    commonFixedGenerators R G V ρ hρ hfin
  obtain ⟨K, hKB, hK⟩ := hB.mem_iff.mp
    (Filter.inter_mem hU (F.isOpen.mem_nhds F.one_mem))
  have hKF : K ≤ F.toSubgroup := fun x hx => (hK hx).2
  refine ⟨n, v, K, hKB, (fun x hx => (hK hx).1), hgen, ?_, ?_⟩
  · intro i g
    exact hfix i ⟨g, hKF g.property⟩
  · intro L hL S hS
    exact hgenerate L (hL.trans hKF) S hS

/-- The two subgroup refinements of the published common-generator result. -/
theorem refinedFixedGenerators :
    RefinedFixedGeneratorsStatement.{uR, uG, uV} :=
  ⟨commonCompactOpenNormalGenerators, commonBasisFixedGenerators⟩

end Langlands
