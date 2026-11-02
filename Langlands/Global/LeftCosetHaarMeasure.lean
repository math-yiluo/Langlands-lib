import Langlands.Global.LeftCosetFundamentalDomain
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Haar measures on discrete left quotients

The fundamental-domain quotient measure is nonzero and locally finite when the
ambient invariant measure has those properties. Its Haar specialization uses
the actual ambient Haar measure.
-/

noncomputable section

universe u

open MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] (Γ : Subgroup H) [MeasurableSpace H]

omit [MeasurableSpace H] in
theorem preimage_image_mk (A : Set H) :
    mk Γ ⁻¹' (mk Γ '' A) = ⋃ γ : Γ, γ • A :=
  MulAction.quotient_preimage_image_eq_union_mul A (G := Γ)

section Countable

variable [Countable Γ] [MeasurableConstSMul Γ H]

theorem measurableSet_image_mk {A : Set H} (hA : MeasurableSet A) :
    MeasurableSet (mk Γ '' A) := by
  rw [measurableSet_quotient, Quotient.mk''_eq_mk]
  change MeasurableSet (mk Γ ⁻¹' (mk Γ '' A))
  rw [preimage_image_mk Γ]
  exact MeasurableSet.iUnion fun γ : Γ => hA.const_smul γ

variable (ν : Measure H) [SMulInvariantMeasure Γ H ν]
  {s : Set H} (hs : IsFundamentalDomain Γ s ν)

include hs

theorem quotientMeasure_image_le {A : Set H} (hA : MeasurableSet A) :
    quotientMeasure Γ ν s (mk Γ '' A) ≤ ν A := by
  rw [quotientMeasure_apply Γ ν s (measurableSet_image_mk Γ hA)]
  rw [preimage_image_mk Γ, iUnion_inter, hs.measure_eq_tsum A]
  exact measure_iUnion_le _

omit [MeasurableConstSMul Γ H] in
theorem quotientMeasure_ne_zero (hν : ν ≠ 0) :
    quotientMeasure Γ ν s ≠ 0 := by
  intro hzero
  apply hs.measure_ne_zero hν
  simpa using congrArg (fun μ : Measure (Langlands.Global.LeftCosetSpace Γ) => μ univ) hzero

variable [TopologicalSpace H] [IsTopologicalGroup H] [BorelSpace H]

theorem isLocallyFiniteMeasure_quotientMeasure [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (quotientMeasure Γ ν s) := by
  refine ⟨fun q => ?_⟩
  obtain ⟨x, rfl⟩ := mk_surjective Γ q
  obtain ⟨U, hxU, hU, hνU⟩ := ν.exists_isOpen_measure_lt_top x
  exact ⟨mk Γ '' U,
    ((isOpenQuotientMap_mk Γ).isOpenMap _ hU).mem_nhds ⟨x, hxU, rfl⟩,
    (quotientMeasure_image_le Γ ν hs hU.measurableSet).trans_lt hνU⟩

end Countable

section Discrete

variable [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [BorelSpace H] (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H)
  [ν.IsMulLeftInvariant]

theorem discreteQuotientMeasure_ne_zero (hν : ν ≠ 0) :
    discreteQuotientMeasure Γ hΓ ν ≠ 0 := by
  let := countable_of_isDiscrete Γ hΓ
  exact quotientMeasure_ne_zero Γ ν (isFundamentalDomain Γ hΓ ν) hν

theorem isLocallyFiniteMeasure_discreteQuotientMeasure [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (discreteQuotientMeasure Γ hΓ ν) := by
  let := countable_of_isDiscrete Γ hΓ
  exact isLocallyFiniteMeasure_quotientMeasure Γ ν (isFundamentalDomain Γ hΓ ν)

end Discrete

section Regularity

variable [TopologicalSpace H] [IsTopologicalGroup H] [BorelSpace H]
  [LocallyCompactSpace H] [PolishSpace H]
  (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H) [ν.IsMulLeftInvariant]

theorem regular_discreteQuotientMeasure [IsLocallyFiniteMeasure ν] :
    (discreteQuotientMeasure Γ hΓ ν).Regular := by
  let : IsClosed (Γ : Set H) := Γ.isClosed_of_isDiscrete hΓ
  let := quotient_borelSpace Γ
  let := isLocallyFiniteMeasure_discreteQuotientMeasure Γ hΓ ν
  infer_instance

end Regularity

section Haar

variable [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [BorelSpace H] [LocallyCompactSpace H]

/-- The discrete left quotient of the actual ambient Haar measure. -/
def haarQuotientMeasure (hΓ : IsDiscrete (Γ : Set H)) :
    Measure (Langlands.Global.LeftCosetSpace Γ) :=
  discreteQuotientMeasure Γ hΓ (Measure.haar : Measure H)

theorem haarQuotientMeasure_ne_zero (hΓ : IsDiscrete (Γ : Set H)) :
    haarQuotientMeasure Γ hΓ ≠ 0 :=
  discreteQuotientMeasure_ne_zero Γ hΓ Measure.haar (NeZero.ne _)

theorem isLocallyFiniteMeasure_haarQuotientMeasure (hΓ : IsDiscrete (Γ : Set H)) :
    IsLocallyFiniteMeasure (haarQuotientMeasure Γ hΓ) :=
  isLocallyFiniteMeasure_discreteQuotientMeasure Γ hΓ Measure.haar

theorem measurePreserving_rightTranslate_haarQuotientMeasure
    [(Measure.haar : Measure H).IsMulRightInvariant]
    (hΓ : IsDiscrete (Γ : Set H)) (g : H) :
    MeasurePreserving (rightTranslate Γ g) (haarQuotientMeasure Γ hΓ)
      (haarQuotientMeasure Γ hΓ) :=
  measurePreserving_rightTranslate_discrete Γ hΓ Measure.haar g

end Haar

section HaarRegularity

variable [TopologicalSpace H] [IsTopologicalGroup H] [BorelSpace H]
  [LocallyCompactSpace H] [PolishSpace H]

theorem regular_haarQuotientMeasure (hΓ : IsDiscrete (Γ : Set H)) :
    (haarQuotientMeasure Γ hΓ).Regular :=
  regular_discreteQuotientMeasure Γ hΓ Measure.haar

end HaarRegularity

end Langlands.Global.LeftCosetSpace
