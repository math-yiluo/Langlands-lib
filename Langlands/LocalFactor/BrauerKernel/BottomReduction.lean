import Langlands.LocalFactor.BrauerKernel.StandaloneBridge
import Langlands.LocalFactor.CommonClosureCoherence
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-! # Reduction of the Brauer kernel identity to the bottom field -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open VirtualRepresentation CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A generator over `E`, regarded as a generator over the bottom field. -/
def Generator.toBottom {E : Extension F} (g : Generator F E) :
    Generator F (Correspondence.baseExtension F) where
  extension := g.extension
  inclusion := baseExtension_le F _
  first := g.first
  second := g.second

/-- Inducing an actual relation over `E` to the bottom field gives an actual relation. -/
theorem presentationMap_mapDomain_toBottom (e : ReciprocityFamily F) (E : Extension F)
    (z : Presentation F E) (hz : presentationMap.{uF, uV} F e E z = 0) :
    presentationMap.{uF, uV} F e (Correspondence.baseExtension F)
      (z.mapDomain (Generator.toBottom F)) = 0 := by
  apply Subtype.ext
  change virtualPresentation F e _ _ = 0
  have hz' : virtualPresentation.{uF, uV} F e E z = 0 := congrArg Subtype.val hz
  have hgen : ∀ g : Generator F E,
      generatorClass.{uF, uV} F e _ (Generator.toBottom F g) =
        induce F (Correspondence.baseExtension F) E (baseExtension_le F E)
          (generatorClass F e E g) := by
    intro g
    rw [generatorClass, generatorClass, induce_trans]
    rfl
  rw [virtualPresentation, Finsupp.linearCombination_mapDomain]
  calc Finsupp.linearCombination ℤ (generatorClass.{uF, uV} F e _ ∘ Generator.toBottom F) z
      = induce F (Correspondence.baseExtension F) E (baseExtension_le F E)
          (virtualPresentation F e E z) := by
        rw [virtualPresentation, Finsupp.linearCombination_apply,
          Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, map_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_zsmul, Function.comp_apply, hgen]
    _ = 0 := by rw [hz', map_zero]

/-- The generator value over the bottom field equals the generator value over `E` for the
trace of the bottom-field character. -/
theorem generatorValue_toBottom (E : Extension F)
    (ψ : AdditiveCharacter F (Correspondence.baseExtension F)) (measures : HaarFamily F)
    (g : Generator F E) :
    generatorValue F _ ψ measures (Generator.toBottom F g) =
      generatorValue F E (traceCharacter F _ E (baseExtension_le F E) ψ) measures g := by
  change (fieldData F g.extension).abelianEpsilonRatio g.first g.second
      (traceCharacter F _ g.extension (baseExtension_le F _) ψ) (measures g.extension) =
    (fieldData F g.extension).abelianEpsilonRatio g.first g.second
      (traceCharacter F E g.extension g.inclusion
        (traceCharacter F _ E (baseExtension_le F E) ψ)) (measures g.extension)
  rw [← traceCharacter_trans]

/-- **Reduction to the bottom field.** If the abelian epsilon evaluation kills every actual
relation over the bottom field, for every additive character and Haar family, then it
kills every actual relation over every intermediate field. -/
theorem evaluationMap_eq_zero_of_bottom (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e)
    (hbot : ∀ z' : Presentation F (Correspondence.baseExtension F),
      presentationMap.{uF, uV} F e _ z' = 0 →
      ∀ (ψ' : AdditiveCharacter F (Correspondence.baseExtension F)) (measures' : HaarFamily F),
        evaluationMap F _ ψ' measures' z' = 0)
    (E : Extension F) (ψ : AdditiveCharacter F E) (measures : HaarFamily F)
    (z : Presentation F E) (hz : presentationMap.{uF, uV} F e E z = 0) :
    evaluationMap F E ψ measures z = 0 := by
  obtain ⟨ψ₀⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists
    ((Correspondence.baseExtension F).asPadicField (p := p))
    (fieldData F (Correspondence.baseExtension F))
  rw [evaluationMap_additiveCharacter_independent.{uF, uV} F e he E
    (traceCharacter F _ E (baseExtension_le F E) ψ₀) ψ measures z hz]
  have hb := hbot _ (presentationMap_mapDomain_toBottom.{uF, uV} F e E z hz) ψ₀ measures
  rw [evaluationMap, Finsupp.linearCombination_mapDomain] at hb
  rw [← hb, evaluationMap]
  refine congrArg (fun f => Finsupp.linearCombination ℤ f z) (funext fun g => ?_)
  rw [Function.comp_apply, generatorValue_toBottom]

end Langlands.LocalFactor.NonabelianBrauer
