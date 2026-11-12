import Langlands.ClassFieldTheory.Local.IntermediateReciprocityTransport
import Langlands.ClassFieldTheory.Local.CommonClosureNormTransport
import Langlands.ClassFieldTheory.Local.CommonClosureConjugationTransport
import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof

/-! # Constructed common-closure reciprocity family and five of its system laws -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.LocalClassField

open Weil Weil.Local LocalFactor.RankOne

universe u

variable {p : ℕ} [Fact p.Prime]

/-- A standalone geometric reciprocity candidate supplied by the published existence theorem. -/
def canonicalStandaloneReciprocity (F : PadicField.{u} p) : ReciprocityCandidate F :=
  Classical.choose ((geometricWeilReciprocityExistenceUniqueness
    p F F.canonicalTopologicalData).exists)

/-- The selected standalone equivalence has the full geometric reciprocity relation. -/
theorem canonicalStandaloneReciprocity_geometric (F : PadicField.{u} p) :
    GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (canonicalStandaloneReciprocity F) :=
  Classical.choose_spec ((geometricWeilReciprocityExistenceUniqueness
    p F F.canonicalTopologicalData).exists)

namespace CommonClosure

variable (F : PadicField.{u} p)

local instance constructionBaseCharZero : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier

variable (e : ∀ E : FiniteIntermediateExtension F.Carrier,
  ReciprocityCandidate (E.asPadicField (p := p)))

/-- On every quotient generator the transported family is standalone reciprocity in inverse coordinates. -/
@[simp] theorem familyOfStandalone_projection
    (E : FiniteIntermediateExtension F.Carrier)
    (w : pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)) :
    familyOfStandalone F e E (abelianizationProjection _ w) =
      reciprocityUnits (E.asPadicField (p := p)) (e E)
        ((intermediateWeilEquiv F E).symm w) := rfl

variable (he : ∀ E : FiniteIntermediateExtension F.Carrier,
  GeometricWeilReciprocityRelation (E.asPadicField (p := p)) (canonicalData F E) (e E))

include he in
/-- All actual common-closure inclusion maps correspond to field norms. -/
theorem normRelation_familyOfStandalone :
    NormRelation F (canonicalData F) (localResidueDegree F) (familyOfStandalone F e) := by
  intro E L h
  apply MonoidHom.ext
  intro a
  induction a using QuotientGroup.induction_on with
  | H w =>
    change reciprocityUnits (E.asPadicField (p := p)) (e E)
      ((intermediateWeilEquiv F E).symm (E.weilInclusion L h (localResidueDegree F) w)) =
        E.unitsNorm L h (reciprocityUnits (L.asPadicField (p := p)) (e L)
          ((intermediateWeilEquiv F L).symm w))
    have hn := CommonClosureTransport.reciprocityUnits_intermediateWeilInclusion
      F E L h (e E) (he E) (e L) (he L) ((intermediateWeilEquiv F L).symm w)
    change reciprocityUnits (E.asPadicField (p := p)) (e E)
      ((intermediateWeilEquiv F E).symm
        (E.weilInclusion L h (localResidueDegree F)
          (intermediateWeilEquiv F L ((intermediateWeilEquiv F L).symm w)))) = _ at hn
    rw [ContinuousMulEquiv.apply_symm_apply] at hn
    exact hn

include he in
/-- All actual ambient Weil conjugations correspond to actual field conjugation. -/
theorem conjugationRelation_familyOfStandalone :
    ConjugationRelation F (canonicalData F) (localResidueDegree F) (familyOfStandalone F e) := by
  intro w E
  apply MonoidHom.ext
  intro a
  induction a using QuotientGroup.induction_on with
  | H x =>
    change reciprocityUnits ((E.conj (localProjection F w)).asPadicField (p := p))
      (e (E.conj (localProjection F w)))
      ((intermediateWeilEquiv F (E.conj (localProjection F w))).symm
        (E.weilConjugation (localResidueDegree F) w x)) =
        E.unitsConjugation (localProjection F w)
          (reciprocityUnits (E.asPadicField (p := p)) (e E)
            ((intermediateWeilEquiv F E).symm x))
    have hc := CommonClosureTransport.reciprocityUnits_intermediateWeilConjugation
      F E w (e E) (he E) (e (E.conj (localProjection F w)))
        (he (E.conj (localProjection F w))) ((intermediateWeilEquiv F E).symm x)
    change reciprocityUnits ((E.conj (localProjection F w)).asPadicField (p := p))
      (e (E.conj (localProjection F w)))
      ((intermediateWeilEquiv F (E.conj (localProjection F w))).symm
        (E.weilConjugation (localResidueDegree F) w
          (intermediateWeilEquiv F E ((intermediateWeilEquiv F E).symm x)))) = _ at hc
    rw [ContinuousMulEquiv.apply_symm_apply] at hc
    exact hc

include he in
/-- The base-field normalization holds with every supplied base topological datum. -/
theorem normalizationRelation_familyOfStandalone (T : F.TopologicalData) :
    NormalizationRelation F (canonicalData F) (localResidueDegree F) T
      (familyOfStandalone F e) := by
  intro E a
  induction a using QuotientGroup.induction_on with
  | H w =>
    change (canonicalData F E).normalizedAbs
      (familyOfStandalone F e E (abelianizationProjection _ w) : E.field) =
      (T.residueCardinality : ℝ) ^ (-localDegreeInt F w)
    rw [familyOfStandalone_projection]
    exact CommonClosureTransport.normalizedAbs_intermediateWeilEquiv_symm F E T (e E) (he E) w

/-- A single actual common-closure candidate family constructed without a reciprocity premise. -/
def constructedReciprocityFamily :
    CandidateFamily F (canonicalData F) (localResidueDegree F) :=
  familyOfStandalone F (fun E => canonicalStandaloneReciprocity (E.asPadicField (p := p)))

/-- The constructed family satisfies the actual norm square. -/
theorem constructedReciprocityFamily_norm :
    NormRelation F (canonicalData F) (localResidueDegree F) (constructedReciprocityFamily F) :=
  normRelation_familyOfStandalone F _
    (fun E => canonicalStandaloneReciprocity_geometric (E.asPadicField (p := p)))

/-- The constructed family satisfies the actual conjugation square. -/
theorem constructedReciprocityFamily_conjugation :
    ConjugationRelation F (canonicalData F) (localResidueDegree F)
      (constructedReciprocityFamily F) :=
  conjugationRelation_familyOfStandalone F _
    (fun E => canonicalStandaloneReciprocity_geometric (E.asPadicField (p := p)))

/-- The constructed family has dense Galois image at every intermediate field. -/
theorem constructedReciprocityFamily_density :
    DensityRelation F (canonicalData F) (localResidueDegree F) (constructedReciprocityFamily F) :=
  densityRelation_familyOfStandalone F _
    (fun E => canonicalStandaloneReciprocity_geometric (E.asPadicField (p := p)))

/-- The constructed family has the actual open-finite-quotient completion comparison. -/
theorem constructedReciprocityFamily_completion :
    CompletionRelation F (canonicalData F) (localResidueDegree F) (constructedReciprocityFamily F) :=
  completionRelation_familyOfStandalone F _
    (fun E => canonicalStandaloneReciprocity_geometric (E.asPadicField (p := p)))

/-- The constructed family is normalized for every supplied base topological datum. -/
theorem constructedReciprocityFamily_normalization (T : F.TopologicalData) :
    NormalizationRelation F (canonicalData F) (localResidueDegree F) T
      (constructedReciprocityFamily F) :=
  normalizationRelation_familyOfStandalone F _
    (fun E => canonicalStandaloneReciprocity_geometric (E.asPadicField (p := p))) T

end CommonClosure
end Langlands.LocalClassField
