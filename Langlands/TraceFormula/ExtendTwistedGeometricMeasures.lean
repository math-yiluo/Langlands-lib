import Langlands.TraceFormula.SingleOrbitGeometricTrace

/-! # Extending an orbital normalization to the rational centralizer quotient -/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory MeasureTheory.Measure Topology
open Langlands.QuotientIntegration Langlands.BaseChange
open scoped ENNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

variable {H : Type*} [Group H] [TopologicalSpace H] [MeasurableSpace H]
  (R : Subgroup H) (θ : H →* H) (r : H) (μH : Measure H)

/-- A prescribed orbital quotient normalization extends to the two compatible
quotients in the geometric trace term using counting on the rational intersection. -/
def ExtendTwistedGeometricMeasuresStatement : Prop :=
  ∀ [IsTopologicalGroup H] [BorelSpace H] [T2Space H] [LocallyCompactSpace H]
    [SecondCountableTopology H],
    Continuous θ → IsDiscrete (R : Set H) →
    let C := twistedCentralizer θ r
    (∀ x y : C, x * y = y * x) →
    ∀ (μC : Measure C) [μC.IsMulRightInvariant]
      [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
      (ν : Measure (LeftQuotient C)),
      IsCompatible C μH μC ν →
      ∃ d : TwistedGeometricMeasures R θ r μH, d.centralizer = μC ∧ d.orbital = ν

theorem extendTwistedGeometricMeasures : ExtendTwistedGeometricMeasuresStatement R θ r μH := by
  intro _ _ _ _ _ hθ hR C hcomm μC hRight hFinite hPos ν hν
  let D := R.subgroupOf C
  have hC : IsClosed (C : Set H) := isClosed_twistedCentralizer θ hθ r
  have hD : IsDiscrete (D : Set C) :=
    hR.preimage continuous_subtype_val.continuousOn Subtype.val_injective
  let : DiscreteTopology D := SetLike.isDiscrete_iff_discreteTopology.mp hD
  let : LocallyCompactSpace C := hC.locallyCompactSpace
  let : SecondCountableTopology C := TopologicalSpace.Subtype.secondCountableTopology (C : Set H)
  let : SecondCountableTopology D := TopologicalSpace.Subtype.secondCountableTopology (D : Set C)
  let : BorelSpace C := Subtype.borelSpace (· ∈ C)
  let : BorelSpace D := Subtype.borelSpace (· ∈ D)
  let : μC.IsMulLeftInvariant := ⟨fun x => by
    have h : (fun y : C => x * y) = fun y => y * x := funext fun y => hcomm x y
    rw [h, map_mul_right_eq_self]⟩
  let : μC.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hFinite
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := hPos }
  let : (Measure.count : Measure D).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hK => Measure.count_apply_lt_top.mpr hK.finite_of_discrete
      toIsMulLeftInvariant := inferInstance
      open_pos := fun _ _ hU => Measure.count_ne_zero hU }
  obtain ⟨νR, hνR⟩ := compatibleMeasureExists D (D.isClosed_of_isDiscrete hD) μC Measure.count
  exact ⟨⟨μC, hRight, hFinite, hPos, ν, νR, hν, hνR⟩, rfl, rfl⟩

variable {R θ r μH} [IsTopologicalGroup H] [BorelSpace H]

/-- A finite compatible rational centralizer covolume gives a nonzero complex scalar. -/
theorem TwistedGeometricMeasures.covolume_ne_zero
    (d : TwistedGeometricMeasures R θ r μH) (hfinite : d.rational Set.univ ≠ ⊤) :
    ((d.rational Set.univ).toReal : ℂ) ≠ 0 := by
  have hpos := ENNReal.toReal_pos
    (fun h => d.rational_compatible.nonzero (Measure.measure_univ_eq_zero.mp h)) hfinite
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

end Langlands.TraceFormula
