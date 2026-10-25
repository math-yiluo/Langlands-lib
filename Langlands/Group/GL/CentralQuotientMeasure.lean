import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.Group.GL.CentralQuotientTopologyProof

/-!
# Haar measure on the full central quotient of a general linear group

Positive characters of the quotient are trivial. Applying this to its modular
character makes every regular Haar measure right invariant.
-/

noncomputable section

namespace Langlands

open Matrix MeasureTheory
open scoped NNReal

universe uF uI

namespace GeneralLinear

variable {F : Type uF} [Field F] {ι : Type uI} [Fintype ι] [DecidableEq ι]

/-- The full central quotient has no nontrivial nonnegative-real characters. -/
theorem centralQuotient_positiveCharacter_eq_one
    (χ : (GeneralLinearGroup ι F ⧸ Subgroup.center (GeneralLinearGroup ι F)) →* ℝ≥0)
    (q : GeneralLinearGroup ι F ⧸ Subgroup.center (GeneralLinearGroup ι F)) :
    χ q = 1 := by
  induction q using Quotient.inductionOn with
  | _ g =>
    apply RankinSelberg.GeneralLinearUnimodularity.character_eq_one
      (χ.comp (QuotientGroup.mk' (Subgroup.center (GeneralLinearGroup ι F))))
    intro a
    have ha : GeneralLinearGroup.scalar ι a ∈ Subgroup.center (GeneralLinearGroup ι F) :=
      Subgroup.mem_center_iff.mpr fun g => (GeneralLinearGroup.scalar_commute a g).symm
    change χ (QuotientGroup.mk (GeneralLinearGroup.scalar ι a)) = 1
    rw [(QuotientGroup.eq_one_iff _).mpr ha, map_one]

variable [TopologicalSpace (GeneralLinearGroup ι F)]
  [IsTopologicalGroup (GeneralLinearGroup ι F)]
  [LocallyCompactSpace (GeneralLinearGroup ι F ⧸ Subgroup.center (GeneralLinearGroup ι F))]
  [MeasurableSpace (GeneralLinearGroup ι F ⧸ Subgroup.center (GeneralLinearGroup ι F))]
  [BorelSpace (GeneralLinearGroup ι F ⧸ Subgroup.center (GeneralLinearGroup ι F))]

/-- Every regular Haar measure on the actual full central quotient is right invariant. -/
theorem haar_centralQuotient_isMulRightInvariant
    (μ : Measure (GeneralLinearGroup ι F ⧸ Subgroup.center (GeneralLinearGroup ι F)))
    [μ.IsHaarMeasure] [μ.Regular] : Measure.IsMulRightInvariant μ := by
  constructor
  intro q
  have : (Measure.map (fun x => x * q) μ).Regular :=
    Measure.Regular.map (μ := μ) (Homeomorph.mulRight q)
  rw [Measure.isMulLeftInvariant_eq_smul_of_regular
    (Measure.map (fun x => x * q) μ) μ,
    ← Measure.modularCharacterFun_eq_haarScalarFactor]
  change Measure.modularCharacter q • μ = μ
  rw [centralQuotient_positiveCharacter_eq_one, one_smul]

/-- An actual Haar measure on `GL` modulo its full center, with no chosen normalization. -/
def centralQuotientHaar :
    Measure (GeneralLinearGroup ι F ⧸ Subgroup.center (GeneralLinearGroup ι F)) :=
  Measure.haar

instance centralQuotientHaar_isHaarMeasure :
    (centralQuotientHaar (F := F) (ι := ι)).IsHaarMeasure :=
  inferInstanceAs Measure.haar.IsHaarMeasure

instance centralQuotientHaar_regular :
    (centralQuotientHaar (F := F) (ι := ι)).Regular :=
  inferInstanceAs Measure.haar.Regular

instance centralQuotientHaar_isMulRightInvariant :
    Measure.IsMulRightInvariant (centralQuotientHaar (F := F) (ι := ι)) :=
  haar_centralQuotient_isMulRightInvariant _

end GeneralLinear

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Every Borel Haar measure on the full central quotient of an actual p-adic
general linear group is right invariant, for every rank including zero. -/
theorem centralQuotientHaar_rightInvariant (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (GeneralLinear n F.Carrier ⧸
        Subgroup.center (GeneralLinear n F.Carrier))]
      [BorelSpace (GeneralLinear n F.Carrier ⧸
        Subgroup.center (GeneralLinear n F.Carrier))]
      (μ : Measure (GeneralLinear n F.Carrier ⧸
        Subgroup.center (GeneralLinear n F.Carrier))) [μ.IsHaarMeasure],
      Measure.IsMulRightInvariant μ := by
  let := T.topology
  intro _ _ μ _
  let := T.generalLinearTopologicalGroup n
  let Q := GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)
  have h := (glBlockCentralQuotientTopology p F T n).1
  let : T2Space Q := h.2.1
  let : LocallyCompactSpace Q := h.2.2.1
  let : SecondCountableTopology Q := h.2.2.2.1
  exact GeneralLinear.haar_centralQuotient_isMulRightInvariant μ

end PadicField.TopologicalData

end Langlands
