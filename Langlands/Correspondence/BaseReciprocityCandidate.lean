import Langlands.Correspondence.BaseReciprocityCoherence
import Langlands.Correspondence.RankOneEpsilonCharacterTransport
import Langlands.LocalClassField.AbelianizationTransport

/-! # The actual base component of a supplied common-closure reciprocity family -/

noncomputable section

universe uF

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure LocalClassField Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance baseCandidateTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance baseCandidateBottomTopology : TopologicalSpace (baseExtension F).field :=
  (fieldData F (baseExtension F)).topology
local instance baseCandidateBottomAlgebra : Algebra (Padic p) (baseExtension F).field :=
  ((baseExtension F).asPadicField (p := p)).algebra

/-- The supplied bottom component, transported through the actual base Weil
and field-unit equivalences. No reciprocity family is chosen. -/
def baseReciprocityCandidate (eC : ReciprocityFamily F) : ReciprocityCandidate F :=
  ((abelianizationCongr (baseWeilEquiv F)).trans (eC (baseExtension F))).trans
    (baseFieldUnitsEquiv F)

/-- This construction satisfies exactly the original base-compatibility predicate. -/
theorem baseReciprocityCandidate_spec (eC : ReciprocityFamily F) :
    IsBaseReciprocity F (baseReciprocityCandidate F eC) eC := by
  intro w
  rfl

/-- The supplied family determines exactly one compatible standalone candidate. -/
theorem existsUnique_baseReciprocityCandidate (eC : ReciprocityFamily F) :
    ∃! e : ReciprocityCandidate F, IsBaseReciprocity F e eC := by
  refine ⟨baseReciprocityCandidate F eC, baseReciprocityCandidate_spec F eC, ?_⟩
  intro e he
  exact he.candidate_eq F (baseReciprocityCandidate_spec F eC)

/-- Every compatible candidate equals the explicitly transported base component. -/
theorem isBaseReciprocity_iff_eq_baseReciprocityCandidate
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F) :
    IsBaseReciprocity F e eC ↔ e = baseReciprocityCandidate F eC :=
  IsBaseReciprocity.iff_eq F (baseReciprocityCandidate_spec F eC)

/-- The normalized family gives the actual base absolute-value formula on
standalone Weil elements through the constructed candidate. -/
theorem normalizedAbs_baseReciprocityCandidate
    (eC : ReciprocityFamily F) (he : NormalizedReciprocity F eC)
    (w : localWeilGroup F) :
    F.canonicalTopologicalData.normalizedAbs
        (reciprocityHom F (baseReciprocityCandidate F eC) w : F.Carrier) =
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-localDegreeInt F w) := by
  have h := he.2 (baseExtension F)
    (abelianizationProjection (weilSubgroup F (baseExtension F)) (baseWeilEquiv F w))
  change (fieldData F (baseExtension F)).normalizedAbs
      ((reciprocityUnits F eC (baseExtension F) (baseWeilEquiv F w) :
        (baseExtension F).fieldˣ) : (baseExtension F).field) =
    (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-localDegreeInt F w) at h
  have hm := PadicField.CanonicalTransport.normalizedAbs_map
    ((baseExtension F).asPadicField (p := p)) F (baseFieldPadicEquiv F)
    ((reciprocityUnits F eC (baseExtension F) (baseWeilEquiv F w) :
      (baseExtension F).fieldˣ) : (baseExtension F).field)
  change F.canonicalTopologicalData.normalizedAbs
      (reciprocityHom F (baseReciprocityCandidate F eC) w : F.Carrier) =
    (fieldData F (baseExtension F)).normalizedAbs
      ((reciprocityUnits F eC (baseExtension F) (baseWeilEquiv F w) :
        (baseExtension F).fieldˣ) : (baseExtension F).field) at hm
  exact hm.trans h

/-- Only the geometric order normalization is concluded here; the full
geometric reciprocity relation additionally contains finite norm-residue laws. -/
theorem geometricOrder_baseReciprocityCandidate
    (eC : ReciprocityFamily F) (he : NormalizedReciprocity F eC) :
    GeometricOrderRelation F.canonicalTopologicalData (localResidueDegree F)
      (baseReciprocityCandidate F eC) := by
  apply MonoidHom.ext
  intro a
  refine QuotientGroup.induction_on a ?_
  intro w
  apply Multiplicative.toAdd.injective
  change F.canonicalTopologicalData.ord
      (reciprocityHom F (baseReciprocityCandidate F eC) w : F.Carrier) = localDegreeInt F w
  have h := normalizedAbs_baseReciprocityCandidate F eC he w
  rw [F.canonicalTopologicalData.normalizedAbs_of_ne_zero
    (reciprocityHom F (baseReciprocityCandidate F eC) w).ne_zero] at h
  have hq : (1 : ℝ) < (F.canonicalTopologicalData.residueCardinality : ℝ) := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  exact neg_injective (zpow_right_injective₀ (zero_lt_one.trans hq) (ne_of_gt hq) h)

/-- The same order normalization holds for every supplied compatible candidate. -/
theorem geometricOrder_of_isBaseReciprocity
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC) (he : NormalizedReciprocity F eC) :
    GeometricOrderRelation F.canonicalTopologicalData (localResidueDegree F) e := by
  rw [(isBaseReciprocity_iff_eq_baseReciprocityCandidate F e eC).1 h]
  exact geometricOrder_baseReciprocityCandidate F eC he

end Langlands.Correspondence
