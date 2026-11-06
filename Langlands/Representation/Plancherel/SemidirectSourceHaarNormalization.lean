import Langlands.Representation.Plancherel.SemidirectSourceGamma
import Langlands.Analysis.Local.SubgroupCompactOpenHaar

/-! # The common compact normalization in semidirect source coordinates -/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz Haar

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Compact factorization is exactly stability of the compact parabolic
intersection under the actual Levi projection. -/
theorem semidirect_compact_split_iff (K : Subgroup G) :
    (∀ (m : M) (u : U),
      (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K) ↔
    (∀ p : P, (p : G) ∈ K → (h.projection p : G) ∈ K) := by
  constructor
  · intro hs p hpk
    let u : U := ⟨(h.projection p : G)⁻¹ * (p : G), h.projection_inv_mul_mem p⟩
    have hprod : (h.projection p : G) * (u : G) ∈ K := by
      simpa only [u, mul_inv_cancel_left] using hpk
    exact ((hs (h.projection p) u).mp hprod).1
  · intro hs m u
    constructor
    · intro hmu
      let p : P := ⟨(m : G) * (u : G),
        P.mul_mem (h.levi_le m.property) (h.unipotent_le u.property)⟩
      have hm : (m : G) ∈ K := by
        have hp := hs p hmu
        change (h.projection
          (⟨(m : G), h.levi_le m.property⟩ *
            ⟨(u : G), h.unipotent_le u.property⟩) : G) ∈ K at hp
        simpa only [h.projection_mul m u] using hp
      exact ⟨hm, by
        simpa only [inv_mul_cancel_left] using K.mul_mem (K.inv_mem hm) hmu⟩
    · rintro ⟨hm, hu⟩
      exact K.mul_mem hm hu

variable [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
  [SecondCountableTopology G]
  (hp : Continuous h.projection)
  (hP : IsClosed (P : Set G)) (hM : IsClosed (M : Set G))
  (hU : IsClosed (U : Set G))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

local instance subgroupSecondCountable (H : Subgroup G) : SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set G)

/-- The existing common-compact subgroup Haar measures give a regular
parabolic product measure through the canonical semidirect homeomorphism. -/
theorem semidirectSourceParabolicMeasure_subgroupHaar_regular :
    (semidirectSourceParabolicMeasure h hp
      (subgroupCompactOpenHaar K hK M hM)
      (subgroupCompactOpenHaar K hK U hU)).Regular := by
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  unfold semidirectSourceParabolicMeasure
  exact Measure.Regular.map (h.coordinates hp)

include hP in
/-- If the actual compact intersection factors, the normalized product
measure is exactly the source-normalized Haar on the original parabolic. -/
theorem semidirectSourceParabolicMeasure_eq_subgroupHaar
    (hKsplit : ∀ (m : M) (u : U),
      (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K) :
    semidirectSourceParabolicMeasure h hp
      (subgroupCompactOpenHaar K hK M hM)
      (subgroupCompactOpenHaar K hK U hU) =
        subgroupCompactOpenHaar K hK P hP := by
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let μM := subgroupCompactOpenHaar K hK M hM
  let μU := subgroupCompactOpenHaar K hK U hU
  let μP := semidirectSourceParabolicMeasure h hp μM μU
  let : μP.IsHaarMeasure :=
    semidirectSourceParabolicMeasure_isHaarMeasure h hp μM μU
  let : μP.Regular :=
    semidirectSourceParabolicMeasure_subgroupHaar_regular h hp hM hU K hK
  exact compactOpenHaarAlong_eq_of_mass_one K hK P.subtype
    hP.isClosedEmbedding_subtypeVal μP
    (semidirectSourceParabolicMeasure_compact h hp μM μU K hKsplit
      (subgroupCompactOpenHaar_mass K hK M hM)
      (subgroupCompactOpenHaar_mass K hK U hU))

variable (V : Subgroup G) (hV : IsClosed (V : Set G))

/-- The source open-cell constant using the existing mass-one Haar measures
on the original closed parabolic and opposite subgroup. -/
def compactNormalizedSourceGamma : ℝ≥0∞ :=
  openCellConstant (subgroupCompactOpenHaar K hK P hP)
    (subgroupCompactOpenHaar K hK V hV) K

include hP in
/-- Canonical semidirect coordinates preserve the exact common-compact
source gamma, with no residual factor. -/
theorem semidirectSourceGamma_eq_compactNormalizedSourceGamma
    (hKsplit : ∀ (m : M) (u : U),
      (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K) :
    semidirectSourceGamma h hp
      (subgroupCompactOpenHaar K hK M hM)
      (subgroupCompactOpenHaar K hK U hU)
      (subgroupCompactOpenHaar K hK V hV) K =
        compactNormalizedSourceGamma hP K hK V hV := by
  unfold semidirectSourceGamma compactNormalizedSourceGamma
  rw [semidirectSourceParabolicMeasure_eq_subgroupHaar h hp hP hM hU K hK hKsplit]

end Langlands.Plancherel
