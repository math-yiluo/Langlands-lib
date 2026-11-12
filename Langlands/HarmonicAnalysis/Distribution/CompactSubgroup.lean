import Langlands.HarmonicAnalysis.Distribution.Haar
import Langlands.HarmonicAnalysis.Distribution.TopologicalSupport

/-! # Renard II.3.11: normalized Haar distributions on compact subgroups -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The actual normalized Haar integral on a compact subgroup, evaluated on
ambient scalar tests. No openness assumption on the subgroup is made. -/
def compactSubgroupDistribution (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    Distribution G := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haarMeasure ⊤
  exact
    { toFun := fun f => ∫ k : K, f k.val ∂μ
      map_add' := fun f g => integral_add
        ((f.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        ((g.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c _ }

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- The integral vanishes on every test vanishing on the subgroup. -/
theorem compactSubgroupDistribution_mem_supportedOn (K : Subgroup G)
    (hK : IsCompact (K : Set G)) :
    compactSubgroupDistribution K hK ∈ supportedOn (K : Set G) := by
  intro f hf
  change (∫ k : K, f k.val ∂_) = 0
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun k => hf k.val k.property

/-- Renard's normalized `e_K`, in the existing compact-support submodule. -/
def compactSubgroupHaar (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    compactlySupported (X := G) :=
  ⟨compactSubgroupDistribution K hK,
    hK.of_isClosed_subset (isClosed_support _)
      (support_subset_of_mem_supportedOn hK.isClosed
        (compactSubgroupDistribution_mem_supportedOn K hK))⟩

@[simp]
theorem coe_compactSubgroupHaar (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    (compactSubgroupHaar K hK : Distribution G) = compactSubgroupDistribution K hK := rfl

/-- The formula uses the Borel Haar measure on the actual compact subgroup,
normalized on its whole underlying group by Mathlib's `haarMeasure ⊤`. -/
theorem compactSubgroupHaar_apply (K : Subgroup G) (hK : IsCompact (K : Set G))
    (f : SchwartzBruhat G) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    letI : MeasurableSpace K := borel K
    letI : BorelSpace K := ⟨rfl⟩
    (compactSubgroupHaar K hK : Distribution G) f =
      ∫ k : K, f k.val ∂(Measure.haarMeasure ⊤) := rfl

end Langlands.HarmonicAnalysis.Distribution
