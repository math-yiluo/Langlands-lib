import Langlands.Representation.Classification.OppositeJacquetReciprocity
import Langlands.Representation.Classification.DiscreteSeriesInductionForms
import Langlands.Representation.Classification.DiscreteSeriesOppositeToUpperProof
import Langlands.Representation.Classification.TemperedDiscreteSeriesJacquetQuotientProof

/-!
# Discrete-series summands of irreducible tempered GL representations

Opposite Jacquet occurrence yields the opposite embedding by the proved
quotient criterion and reciprocity. The same-sigma comparison gives the
upper embedding, and square-integrable induced semisimplicity splits both.
-/

noncomputable section

namespace Langlands

universe uF uV uW

/-- A discrete-series representation occurs in the opposite normalized
Jacquet module of an irreducible tempered representation exactly when the
latter splits off both actual semisimple normalized inductions. -/
theorem glTemperedDiscreteSeriesSummand :
    GLTemperedDiscreteSeriesSummandStatement.{uF, uV, uW} := by
  intro p hp F T
  let := T.topology
  intro n hn B
  let := T.leviTopologicalGroup B
  dsimp only
  intro mQ bQ μ hμ V aV mV W aW mW π σ hπ hπtempered hσ hσsquare
  change
    (∃ S : Subrepresentation (OppositeSupport.jacquetAction T B π),
      ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) ↔
    Representation.IsSemisimpleRepresentation (T.normalizedParabolicInduced B σ) ∧
    Representation.IsSemisimpleRepresentation
      (T.normalizedOppositeParabolicInduced B σ) ∧
    (∃ (j : π.IntertwiningMap (T.normalizedParabolicInduced B σ))
      (r : (T.normalizedParabolicInduced B σ).IntertwiningMap π),
      r.comp j = Representation.IntertwiningMap.id π) ∧
    (∃ (j : π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ))
      (r : (T.normalizedOppositeParabolicInduced B σ).IntertwiningMap π),
      r.comp j = Representation.IntertwiningMap.id π)
  constructor
  · intro hoccurs
    have hπsmooth : IsSmooth π := hπtempered.isAdmissible.1
    have hq := glTemperedDiscreteSeriesJacquetQuotient.{uF, uV, uW}
      p F T n hn B μ V W π σ hπ hπtempered hσ hσsquare
    change
      (∃ S : Subrepresentation (OppositeSupport.jacquetAction T B π),
        ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q) ↔
      (∃ q : (OppositeSupport.jacquetAction T B π).IntertwiningMap σ,
        Function.Surjective q) at hq
    obtain ⟨jopposite, hjopposite⟩ :=
      (OppositeSupport.quotient_iff_embedding T B π σ hπsmooth hπ hσ).mp
        (hq.mp hoccurs)
    obtain ⟨_, jupper, hjupper⟩ :=
      glTemperedDiscreteSeriesOppositeToUpper.{uF, uV, uW}
        p F T n hn B μ V W π σ hπ hπtempered hσ hσsquare
        ⟨jopposite, hjopposite⟩
    obtain ⟨hssupper, hssopposite⟩ :=
      isSemisimple_bothInduced_of_squareIntegrable.{uF, uW}
        T B hn μ σ hσ hσsquare
    exact ⟨hssupper, hssopposite,
      ⟨jupper, (semisimpleRetraction hssupper jupper hjupper).val,
        (semisimpleRetraction hssupper jupper hjupper).property⟩,
      ⟨jopposite, (semisimpleRetraction hssopposite jopposite hjopposite).val,
        (semisimpleRetraction hssopposite jopposite hjopposite).property⟩⟩
  · rintro ⟨_, _, _, jopposite, ropposite, hsplit⟩
    apply OppositeSupport.occurs_of_embedding T B π σ hπ hσ jopposite
    intro v w hvw
    have hs (x : V) : ropposite (jopposite x) = x :=
      congrArg (fun f : π.IntertwiningMap π => f x) hsplit
    rw [← hs v, ← hs w, hvw]

end Langlands
