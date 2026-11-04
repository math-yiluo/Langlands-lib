import Langlands.Representation.RankinSelberg.Measures
import Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Haar normalization at one common ambient compact open -/

noncomputable section

namespace Langlands.Haar

open MeasureTheory MeasureTheory.Measure
open RankinSelberg

universe uG uH uL

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]
  (ι : H →* G) (hι : Topology.IsClosedEmbedding (ι : H → G))

/-- The compact open on an actual embedded carrier is the inverse image of
the one fixed ambient compact open. -/
def compactOpenPreimage : OpenSubgroup H :=
  K.comap ι hι.continuous

include hK in
omit [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] in
theorem compactOpenPreimage_isCompact :
    IsCompact (compactOpenPreimage K ι hι : Set H) :=
  hι.isCompact_preimage hK

/-- Haar on the actual carrier, with the common ambient compact open of
mass one. This reuses the existing normalized Haar constructor. -/
def compactOpenHaarAlong : Measure H :=
  normalizedCompactOpenHaar (compactOpenPreimage K ι hι)
    (compactOpenPreimage_isCompact K hK ι hι)

instance compactOpenHaarAlong_isHaarMeasure :
    IsHaarMeasure (compactOpenHaarAlong K hK ι hι) := by
  unfold compactOpenHaarAlong
  infer_instance

instance compactOpenHaarAlong_regular :
    (compactOpenHaarAlong K hK ι hι).Regular := by
  unfold compactOpenHaarAlong
  infer_instance

/-- The normalization is on the original embedded elements, not on a new
ambient measure restricted to the carrier. -/
@[simp] theorem compactOpenHaarAlong_mass :
    compactOpenHaarAlong K hK ι hι {h : H | ι h ∈ K} = 1 :=
  normalizedCompactOpenHaar_self _ _

section Uniqueness

variable [LocallyCompactSpace G]

/-- Every regular left-invariant measure with the prescribed source mass
is exactly the constructed measure. -/
theorem compactOpenHaarAlong_eq_of_mass_one
    (μ : Measure H) [IsMulLeftInvariant μ] [μ.Regular]
    (hmass : μ {h : H | ι h ∈ K} = 1) :
    μ = compactOpenHaarAlong K hK ι hι := by
  let : LocallyCompactSpace H := hι.locallyCompactSpace
  have he := isMulLeftInvariant_eq_smul_of_regular μ
    (compactOpenHaarAlong K hK ι hι)
  have hc : haarScalarFactor μ (compactOpenHaarAlong K hK ι hι) = 1 := by
    apply ENNReal.coe_injective
    have hv := congrArg (fun ν : Measure H => ν {h : H | ι h ∈ K}) he
    simpa only [hmass, Measure.smul_apply, compactOpenHaarAlong_mass,
      ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_one] using hv.symm
  rw [he, hc, one_smul]

/-- Right invariance of the intrinsic source normalization follows from a
genuine regular two-sided Haar measure on the same carrier. -/
theorem compactOpenHaarAlong_isMulRightInvariant
    (μ : Measure H) [IsHaarMeasure μ] [μ.Regular] [IsMulRightInvariant μ] :
    IsMulRightInvariant (compactOpenHaarAlong K hK ι hι) := by
  let : LocallyCompactSpace H := hι.locallyCompactSpace
  rw [isMulLeftInvariant_eq_smul_of_regular (compactOpenHaarAlong K hK ι hι) μ]
  infer_instance

/-- A compact-open cover gives the same right invariance without supplying
a second measure or assuming the desired measure property. -/
theorem compactOpenHaarAlong_isMulRightInvariant_of_cover [T2Space G]
    (hcover : ∀ h : H, ∃ C : OpenSubgroup H, IsCompact (C : Set H) ∧ h ∈ C) :
    IsMulRightInvariant (compactOpenHaarAlong K hK ι hι) := by
  let : LocallyCompactSpace H := hι.locallyCompactSpace
  let : T2Space H := hι.isEmbedding.t2Space
  exact (compactOpenCoverUnimodularity hcover).1 (compactOpenHaarAlong K hK ι hι)

variable {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [MeasurableSpace L] [BorelSpace L]
  (κ : L →* G) (hκ : Topology.IsClosedEmbedding (κ : L → G))
  (e : H ≃ₜ* L) (he : ∀ h : H, κ (e h) = ι h)

include he in
/-- Identifications of actual carriers preserving their ambient elements
preserve the source-normalized Haar measures exactly, with no scalar. -/
theorem measurePreserving_compactOpenHaarAlong :
    MeasurePreserving e (compactOpenHaarAlong K hK ι hι)
      (compactOpenHaarAlong K hK κ hκ) := by
  have : (Measure.map e (compactOpenHaarAlong K hK ι hι)).Regular :=
    Measure.Regular.map e.toHomeomorph
  have : IsHaarMeasure (Measure.map e (compactOpenHaarAlong K hK ι hι)) :=
    e.isHaarMeasure_map _
  refine ⟨e.continuous.measurable, ?_⟩
  apply compactOpenHaarAlong_eq_of_mass_one K hK κ hκ
  have hmeas : Measurable (e : H → L) := e.continuous.measurable
  have hset : MeasurableSet {l : L | κ l ∈ K} :=
    (compactOpenPreimage K κ hκ).isOpen.measurableSet
  rw [Measure.map_apply hmeas hset]
  have hpre : e ⁻¹' {l : L | κ l ∈ K} = {h : H | ι h ∈ K} := by
    ext h
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, he]
  rw [hpre, compactOpenHaarAlong_mass]

end Uniqueness

section Subgroups

variable [IsTopologicalGroup G] (U : Subgroup G) (hU : IsClosed (U : Set G))
  [MeasurableSpace U] [BorelSpace U]

/-- The source normalization on a closed subgroup uses its own Haar
measure and the inverse image of the common ambient compact open. -/
def subgroupCompactOpenHaar : Measure U :=
  compactOpenHaarAlong K hK U.subtype hU.isClosedEmbedding_subtypeVal

instance subgroupCompactOpenHaar_isHaarMeasure :
    IsHaarMeasure (subgroupCompactOpenHaar K hK U hU) := by
  unfold subgroupCompactOpenHaar
  exact compactOpenHaarAlong_isHaarMeasure K hK U.subtype hU.isClosedEmbedding_subtypeVal

instance subgroupCompactOpenHaar_regular :
    (subgroupCompactOpenHaar K hK U hU).Regular := by
  unfold subgroupCompactOpenHaar
  exact compactOpenHaarAlong_regular K hK U.subtype hU.isClosedEmbedding_subtypeVal

@[simp] theorem subgroupCompactOpenHaar_mass :
    subgroupCompactOpenHaar K hK U hU {u : U | (u : G) ∈ K} = 1 :=
  compactOpenHaarAlong_mass K hK U.subtype hU.isClosedEmbedding_subtypeVal

end Subgroups

end Langlands.Haar
