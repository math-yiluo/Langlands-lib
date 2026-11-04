import Langlands.Analysis.Local.SubgroupCompactOpenHaar
import Langlands.Analysis.Local.CompactOpenFactorProduct
import Langlands.Analysis.Local.QuotientMeasureExistence

/-! # Literal factorization with the common compact-open source scale -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure RankinSelberg Haar

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (S : OpenSubgroup G) (hS : IsCompact (S : Set G))
  (H : Subgroup G) (hH : IsClosed (H : Set G))
  [MeasurableSpace H] [BorelSpace H]

section QuotientChoice

variable [T2Space G] [LocallyCompactSpace G]
  [IsMulRightInvariant (normalizedCompactOpenHaar S hS)]
  [IsMulRightInvariant (subgroupCompactOpenHaar S hS H hH)]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]

/-- A specific actual quotient measure for the prescribed source Haar
measures, selected only from the proved compatible-measure existence theorem. -/
def sourceCompactOpenQuotientMeasure : Measure (LeftQuotient H) :=
  Classical.choose (compatibleMeasureExists H hH
    (normalizedCompactOpenHaar S hS) (subgroupCompactOpenHaar S hS H hH))

/-- The selected measure satisfies the genuine complex Weil formula for
the same source-normalized measures used in its definition. -/
theorem sourceCompactOpenQuotientMeasure_isCompatible :
    IsCompatible H (normalizedCompactOpenHaar S hS)
      (subgroupCompactOpenHaar S hS H hH)
      (sourceCompactOpenQuotientMeasure S hS H hH) :=
  Classical.choose_spec (compatibleMeasureExists H hH
    (normalizedCompactOpenHaar S hS) (subgroupCompactOpenHaar S hS H hH))

instance sourceCompactOpenQuotientMeasure_regular :
    (sourceCompactOpenQuotientMeasure S hS H hH).Regular :=
  (sourceCompactOpenQuotientMeasure_isCompatible S hS H hH).regular

theorem sourceCompactOpenQuotientMeasure_ne_zero :
    sourceCompactOpenQuotientMeasure S hS H hH ≠ 0 :=
  (sourceCompactOpenQuotientMeasure_isCompatible S hS H hH).nonzero

end QuotientChoice

section Complement

variable (K : Subgroup G) (hK : IsClosed (K : Set G))
  [MeasurableSpace K] [BorelSpace K]

local notation "μG" => normalizedCompactOpenHaar S hS
local notation "μH" => subgroupCompactOpenHaar S hS H hH
local notation "μK" => subgroupCompactOpenHaar S hS K hK
local notation "B" => compactOpenPreimage S K.subtype hK.isClosedEmbedding_subtypeVal

/-- At the common source scale every mass in the explicit correction
scalar is one, so no scalar correction remains. -/
theorem compactOpenFactorScalar_source :
    compactOpenFactorScalar H K μG μH μK S B = 1 := by
  have hB : μK (B : Set K) = 1 := subgroupCompactOpenHaar_mass S hS K hK
  simp only [compactOpenFactorScalar, normalizedCompactOpenHaar_self,
    subgroupCompactOpenHaar_mass, hB, ENNReal.toNNReal_one, one_mul, div_one]

/-- The locally normalized factor is exactly the subgroup's intrinsic
source-normalized Haar measure. -/
theorem compactOpenFactorMeasure_source :
    compactOpenFactorMeasure H K μG μH μK S B = μK := by
  rw [compactOpenFactorMeasure, compactOpenFactorScalar_source S hS H hH K hK,
    one_smul]

variable [T2Space G] [LocallyCompactSpace G]
  [IsMulRightInvariant (subgroupCompactOpenHaar S hS H hH)]
  [IsMulRightInvariant (subgroupCompactOpenHaar S hS K hK)]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  (m : H × K ≃ₜ G) (hm : ∀ p : H × K, m p = p.1.val * p.2.val)
  {ν : Measure (LeftQuotient H)}

include hm in
/-- A supplied compatible quotient is preserved by the literal complement
chart when the common compact open has the supplied local product geometry. -/
theorem IsCompatible.measurePreserving_sourceCompactOpenFactor
    (hν : IsCompatible H μG μH ν)
    (hlocal : m '' ({h : H | (h : G) ∈ S} ×ˢ
      {k : K | (k : G) ∈ S}) = (S : Set G)) :
    MeasurePreserving (factorQuotientHomeomorph H Subtype.val m hm) μK ν := by
  have hB : IsCompact (B : Set K) :=
    compactOpenPreimage_isCompact S hS K.subtype hK.isClosedEmbedding_subtypeVal
  have hc := hν.measurePreserving_compactOpenFactorMeasure_of_localProduct
    H K μG μH μK S B m hm hH hS hB hlocal
  rwa [compactOpenFactorMeasure_source S hS H hH K hK] at hc

include hm in
/-- Ambient second countability discharges all product regularity,
S-finiteness and product Borel premises. The resulting product uses the
original source Haar on each subgroup, with no rescaling. -/
theorem IsCompatible.measurePreserving_sourceCompactOpenProduct
    [scG : SecondCountableTopology G]
    (hν : IsCompatible H μG μH ν)
    (hlocal : m '' ({h : H | (h : G) ∈ S} ×ˢ
      {k : K | (k : G) ∈ S}) = (S : Set G)) :
    MeasurePreserving m ((μH).prod μK) μG := by
  let : SecondCountableTopology H :=
    TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  let : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : LocallyCompactSpace K := hK.locallyCompactSpace
  exact hν.measurePreserving_factorProduct H K m hm μK
    (hν.measurePreserving_sourceCompactOpenFactor S hS H hH K hK m hm hlocal)

end Complement

end Langlands.QuotientIntegration
