import Langlands.Representation.Aubert.CorrectedOrbitCutMeasures
import Langlands.Representation.Aubert.CorrectedSupportOrbitIntegrals

/-! Actual supplied-measure orbit comparison squares on corrected supports. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.Support

open GeneralLinear Geometric Induction MeasureTheory QuotientIntegration HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- Evaluate the actual supplied-measure orbit equivalence on the genuine
radical coinvariants, at a target Levi element. -/
def cutOrbitIntegralValue :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ParabolicOrbitIntegralMeasures F.Carrier B C w →
      Representation.Coinvariants
          ((compactInduced (parabolicOrbitStabilizer F.Carrier B C w)
            (cutOrbitCoefficient T A B C w)).comp
              (C.leviProjection F.Carrier).ker.subtype) →
        C.Levi F.Carrier →
          Representation.Coinvariants (cutOrbitNestedCoefficient T A.representation C w B) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro m z l
  exact eval (parabolicOrbitStagesQuotient F.Carrier B C w)
    (parabolicOrbitIntegratedCoefficient F.Carrier B C w (T.leviHalfModulus B)
      (T.normalizedJacquet B A.representation))
    (T.parabolicOrbitCompactIntegralEquiv B C w m
      ((T.normalizedJacquetFunctor B).obj A) z).val l

/-- Evaluation on an actual compact representative is precisely its genuine
cut integrand integrated against the supplied quotient measure. -/
theorem cutOrbitIntegralValue_mk_integral :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    letI : MeasurableSpace (QuotientIntegration.LeftQuotient
      (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
    ∀ (m : ParabolicOrbitIntegralMeasures F.Carrier B C w)
      (f : CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
        (cutOrbitCoefficient T A B C w)) (l : C.Levi F.Carrier),
      cutOrbitIntegralValue T A B C w m
          (Representation.Coinvariants.mk
            ((compactInduced (parabolicOrbitStabilizer F.Carrier B C w)
              (cutOrbitCoefficient T A B C w)).comp
                (C.leviProjection F.Carrier).ker.subtype) f) l =
        AlgebraicIntegral.integral m.quotient (cutOrbitIntegrand T A B C w f l) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro m f l
  exact T.parabolicOrbitCompactIntegralEquiv_eval_mk B C w m
    ((T.normalizedJacquetFunctor B).obj A) f l

variable (D : BlockShape n) (h : B.cuts ⊆ D.cuts)
  (hw : TypeASolomon.SourceIncreasing B w)

/-- The actual supplied-measure orbit equivalences have the source-cut
coefficient square on every pair of pointwise projected orbit functions. -/
theorem cutOrbitIntegralValue_cutMap :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ (m : ParabolicOrbitIntegralMeasures F.Carrier B C w)
      (fB : CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
        (cutOrbitCoefficient T A B C w))
      (fD : CompactFunctions (parabolicOrbitStabilizer F.Carrier D C w)
        (cutOrbitCoefficient T A D C w)),
      (∀ q : C.parabolic F.Carrier, eval _ _ fD.val q =
        Transition.quotient A.representation (unipotentSubgroup_le_of_cuts_subset h)
          (eval _ _ fB.val q)) →
      ∀ l : C.Levi F.Carrier,
        cutOrbitIntegralValue T A D C w
            (parabolicOrbitIntegralMeasures_cutMap F.Carrier B D C w h hw m)
            (Representation.Coinvariants.mk
              ((compactInduced (parabolicOrbitStabilizer F.Carrier D C w)
                (cutOrbitCoefficient T A D C w)).comp
                  (C.leviProjection F.Carrier).ker.subtype) fD) l =
          cutOrbitCoefficientMap T A.representation B D C w h hw
            (cutOrbitIntegralValue T A B C w m
              (Representation.Coinvariants.mk
                ((compactInduced (parabolicOrbitStabilizer F.Carrier B C w)
                  (cutOrbitCoefficient T A B C w)).comp
                    (C.leviProjection F.Carrier).ker.subtype) fB) l) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier D C w)) := borel _
  intro m fB fD hf l
  let := m.quotientFinite
  have hD := cutOrbitIntegralValue_mk_integral T A D C w
    (parabolicOrbitIntegralMeasures_cutMap F.Carrier B D C w h hw m) fD l
  have hB := cutOrbitIntegralValue_mk_integral T A B C w m fB l
  have hI := cutOrbitStagesIntegral_map T A B D C w h hw m.quotient fB fD hf l
  exact hD.trans (hI.trans (congrArg
    (cutOrbitCoefficientMap T A.representation B D C w h hw) hB.symm))

variable (θ : Set (Equiv.Perm (Fin n)))
  (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
  (hLower : ∀ v ∈ θ \ {w}, ∀ z, inversionLength v < inversionLength z → z ∈ θ \ {w})
  (hwSupport : w ∈ weylSupport B C θ)

/-- For corrected-support representatives, the actual equivalence square has
no pointwise compatibility premise: the canonical cut map supplies it. -/
theorem correctedOrbitRestriction_comparison_cutMap :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ (m : ParabolicOrbitIntegralMeasures F.Carrier B C w)
      (f : (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A)) (l : C.Levi F.Carrier),
      let fD : (correctedInductionSupport T D C θ).representation
          ((T.normalizedJacquetFunctor D).obj A) :=
        ⟨Transition.cutMap T A.representation h f.val,
          cutMap_mem_correctedInductionSupport T A C h θ f.val f.property⟩
      cutOrbitIntegralValue T A D C w
          (parabolicOrbitIntegralMeasures_cutMap F.Carrier B D C w h hw m)
          (Representation.Coinvariants.mk
            ((compactInduced (parabolicOrbitStabilizer F.Carrier D C w)
              (cutOrbitCoefficient T A D C w)).comp
                (C.leviProjection F.Carrier).ker.subtype)
            (correctedOrbitRestriction T A D C θ w hθ hLower
              (weylSupport_mono_source_cuts C h θ hwSupport) fD)) l =
        cutOrbitCoefficientMap T A.representation B D C w h hw
          (cutOrbitIntegralValue T A B C w m
            (Representation.Coinvariants.mk
              ((compactInduced (parabolicOrbitStabilizer F.Carrier B C w)
                (cutOrbitCoefficient T A B C w)).comp
                  (C.leviProjection F.Carrier).ker.subtype)
              (correctedOrbitRestriction T A B C θ w hθ hLower hwSupport f)) l) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro m f l
  apply cutOrbitIntegralValue_cutMap T A B C w D h hw m
  exact correctedOrbitRestriction_cutMap_eval T A B C θ w hθ hLower hwSupport h f

end Langlands.Aubert.Support
