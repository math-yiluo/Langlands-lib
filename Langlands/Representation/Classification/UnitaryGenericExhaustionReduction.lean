import Langlands.Representation.Classification.UnitaryGenericStatement
import Langlands.Representation.Classification.HigherSpehElimination
import Langlands.Representation.Classification.TadicWhittakerReflection
import Langlands.Representation.Classification.TadicLengthOneParameters
import Langlands.Representation.Classification.OrderedMultisegmentHeadClassificationReduction
import Langlands.Representation.Classification.SegmentSpecialParameterUniquenessProof
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationProof

/-! # Unitary generic exhaustion from generic-free Tadic exhaustion

A nondegenerate Tadic building block has Speh length one, hence actual valid
unitary generic parameters. Assembling these over a Tadic factorization of a
generic unitarizable representation gives its actual parameters. The
generic-free exhaustion is the only remaining hypothesis: the ordered-head
classification follows from the proved square-integrable Langlands
classification.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A Tadic building block with a nonzero upper-character functional has
actual valid unitary generic parameters. Ordered-head classification excludes
Speh length greater than one. -/
theorem nonempty_unitaryParameterRealization_of_isTadicBuildingBlock
    (hc : OrderedMultisegmentHeadClassification.{uF,uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ}
    (σ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hσ : IsTadicBuildingBlock F T σ)
    (hf : letI := T.topology
      Whittaker.HasFunctional (N := upperUnipotent n F.Carrier)
        (θ := Whittaker.entrywiseCharacter ψ.complex n) σ.representation) :
    Nonempty (UnitaryParameterRealization.{uF,uV} F T σ) := by
  let := T.topology
  rcases hσ with ⟨d, S, h, hS, ⟨e⟩⟩ | ⟨d, S, α, h, hS, hα0, hα1, ⟨e⟩⟩
  · subst h
    have hfS : Whittaker.HasFunctional (N := upperUnipotent d.degree F.Carrier)
        (θ := Whittaker.entrywiseCharacter ψ.complex d.degree) S.representation :=
      (Whittaker.hasFunctional_iff_of_equiv (SmoothRep.equivOfIso e)).mpr hf
    have h1 := SpehDatum.length_eq_one_of_hasFunctional F T hc ψ d S hS hfS
    exact ⟨(lengthOneSpehParameterRealization F T d S hS h1).ofIso F T e.symm⟩
  · subst h
    have hfC : Whittaker.HasFunctional (N := upperUnipotent (2 * d.degree) F.Carrier)
        (θ := Whittaker.entrywiseCharacter ψ.complex (2 * d.degree))
        (d.complementaryInduced S α).representation :=
      (Whittaker.hasFunctional_iff_of_equiv (SmoothRep.equivOfIso e)).mpr hf
    have hfS := (SpehDatum.hasFunctional_complementaryInduced_iff T ψ d S α).mp hfC
    have h1 := SpehDatum.length_eq_one_of_hasFunctional F T hc ψ d S hS hfS
    exact ⟨(lengthOneComplementaryParameterRealization F T d S hS h1 α hα0 hα1).ofIso
      F T e.symm⟩

/-- Actual valid unitary generic parameters of a generic unitarizable
representation, chosen from a generic-free Tadic factorization. Both
classification inputs are explicit hypotheses. -/
def unitaryGenericParameterRealizationOfTadic
    (hT : TadicUnitaryDualExhaustion.{uF,uV} F T)
    (hc : OrderedMultisegmentHeadClassification.{uF,uV} F T)
    (n : ℕ) (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier))
    (hg : letI := T.topology; Whittaker.IsGeneric ψ n π.representation)
    (hu : letI := T.topology; IsUnitarizable π.representation) :
    UnitaryParameterRealization.{uF,uV} F T π :=
  Classical.choice <| by
    let := T.topology
    obtain ⟨B, σ, hσ, ⟨e⟩⟩ := hT n π hg.1 hu
    have hfπ : Whittaker.HasFunctional (N := upperUnipotent (n + 1) F.Carrier)
        (θ := Whittaker.entrywiseCharacter ψ.complex (n + 1)) π.representation := by
      rw [Whittaker.entrywiseCharacter_eq_standardCharacter]
      exact hg.2.2
    have hfP := (Whittaker.hasFunctional_iff_of_equiv (SmoothRep.equivOfIso e)).mp hfπ
    have hfi := (Whittaker.hasFunctional_finiteProduct_iff.{uF,uV} T ψ B σ).mp hfP
    have R : ∀ i, Nonempty (UnitaryParameterRealization.{uF,uV} F T (σ i)) := fun i =>
      nonempty_unitaryParameterRealization_of_isTadicBuildingBlock F T hc ψ (σ i)
        (hσ i) (hfi i)
    exact ⟨(UnitaryParameterRealization.product F T B σ
      (fun i => Classical.choice (R i))).ofIso F T e⟩

/-- Generic-free Tadic exhaustion and ordered-head classification imply the
exact unitary generic exhaustion proposition. -/
theorem unitaryGenericExhaustion_of_tadic
    (hT : TadicUnitaryDualExhaustion.{uF,uV} F T)
    (hc : OrderedMultisegmentHeadClassification.{uF,uV} F T) :
    UnitaryGenericExhaustion.{uF,uV} F T := by
  intro n ψ π hg hu
  exact (unitaryGenericParameterRealizationOfTadic F T hT hc n ψ π hg hu).exists_datum F T

/-- The same conclusion with ordered-head classification replaced by the
square-integrable Langlands classification, using the published reduction and
the proved special-parameter uniqueness. -/
theorem unitaryGenericExhaustion_of_tadic_of_squareIntegrable
    (hT : TadicUnitaryDualExhaustion.{uF,uV} F T)
    (hs : SquareIntegrableLanglandsClassification.{uF,uV} F T) :
    UnitaryGenericExhaustion.{uF,uV} F T :=
  unitaryGenericExhaustion_of_tadic F T hT
    (orderedMultisegmentHeadClassification_of_squareIntegrable F T hs
      (segmentSpecialParameterUniqueness F T))

/-- Generic-free Tadic exhaustion alone implies the exact unitary generic
exhaustion proposition. -/
theorem unitaryGenericExhaustion_of_tadicUnitaryDualExhaustion
    (hT : TadicUnitaryDualExhaustion.{uF,uV} F T) :
    UnitaryGenericExhaustion.{uF,uV} F T :=
  unitaryGenericExhaustion_of_tadic_of_squareIntegrable F T hT
    (squareIntegrableLanglandsClassification F T)

end Langlands.Classification
