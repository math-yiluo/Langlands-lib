import Langlands.Representation.Aubert.CorrectedOrbitCutComparison
import Langlands.Representation.Aubert.CorrectedOrbitMeasureFamily

/-! Simultaneous actual comparison squares for the coherent measure family. -/

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

/-- Values of the actual orbit equivalence, with the same measure family
chosen simultaneously for all source-increasing shapes. -/
def coherentCutOrbitIntegralValue (hw : TypeASolomon.SourceIncreasing B w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
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
  exact cutOrbitIntegralValue T A B C w (T.parabolicOrbitCoherentMeasures C w B hw)

/-- Every inclusion of admissible source cuts gives the coefficient square
for this single family, without a new choice of measures at either end. -/
theorem coherentCutOrbitIntegralValue_cutMap
    (D : BlockShape n) (h : B.cuts ⊆ D.cuts)
    (hwB : TypeASolomon.SourceIncreasing B w)
    (hwD : TypeASolomon.SourceIncreasing D w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ (fB : CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
        (cutOrbitCoefficient T A B C w))
      (fD : CompactFunctions (parabolicOrbitStabilizer F.Carrier D C w)
        (cutOrbitCoefficient T A D C w)),
      (∀ q : C.parabolic F.Carrier, eval _ _ fD.val q =
        Transition.quotient A.representation (unipotentSubgroup_le_of_cuts_subset h)
          (eval _ _ fB.val q)) →
      ∀ l : C.Levi F.Carrier,
        coherentCutOrbitIntegralValue T A D C w hwD
            (Representation.Coinvariants.mk
              ((compactInduced (parabolicOrbitStabilizer F.Carrier D C w)
                (cutOrbitCoefficient T A D C w)).comp
                  (C.leviProjection F.Carrier).ker.subtype) fD) l =
          cutOrbitCoefficientMap T A.representation B D C w h hwB
            (coherentCutOrbitIntegralValue T A B C w hwB
              (Representation.Coinvariants.mk
                ((compactInduced (parabolicOrbitStabilizer F.Carrier B C w)
                  (cutOrbitCoefficient T A B C w)).comp
                    (C.leviProjection F.Carrier).ker.subtype) fB) l) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro fB fD hf l
  have he := cutOrbitIntegralValue_cutMap T A B C w D h hwB
    (T.parabolicOrbitCoherentMeasures C w B hwB) fB fD hf l
  have hm := congrArg
    (fun m => cutOrbitIntegralValue T A D C w m
      (Representation.Coinvariants.mk
        ((compactInduced (parabolicOrbitStabilizer F.Carrier D C w)
          (cutOrbitCoefficient T A D C w)).comp
            (C.leviProjection F.Carrier).ker.subtype) fD) l)
    (T.parabolicOrbitCoherentMeasures_cutMap C w B D h hwB hwD)
  exact hm.symm.trans he

/-- The actual corrected-support restrictions give the same coherent square
after their canonical support quotient projections. -/
theorem correctedOrbitRestriction_coherent_comparison_cutMap
    (D : BlockShape n) (h : B.cuts ⊆ D.cuts)
    (hwB : TypeASolomon.SourceIncreasing B w)
    (hwD : TypeASolomon.SourceIncreasing D w)
    (θ : Set (Equiv.Perm (Fin n)))
    (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
    (hLower : ∀ v ∈ θ \ {w}, ∀ z, inversionLength v < inversionLength z → z ∈ θ \ {w})
    (hwSupport : w ∈ weylSupport B C θ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ (f : (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A)) (l : C.Levi F.Carrier),
      let fD : (correctedInductionSupport T D C θ).representation
          ((T.normalizedJacquetFunctor D).obj A) :=
        ⟨Transition.cutMap T A.representation h f.val,
          cutMap_mem_correctedInductionSupport T A C h θ f.val f.property⟩
      coherentCutOrbitIntegralValue T A D C w hwD
          (Representation.Coinvariants.mk
            ((compactInduced (parabolicOrbitStabilizer F.Carrier D C w)
              (cutOrbitCoefficient T A D C w)).comp
                (C.leviProjection F.Carrier).ker.subtype)
            (correctedOrbitRestriction T A D C θ w hθ hLower
              (weylSupport_mono_source_cuts C h θ hwSupport) fD)) l =
        cutOrbitCoefficientMap T A.representation B D C w h hwB
          (coherentCutOrbitIntegralValue T A B C w hwB
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
  intro f l
  apply coherentCutOrbitIntegralValue_cutMap T A B C w D h hwB hwD
  exact correctedOrbitRestriction_cutMap_eval T A B C θ w hθ hLower hwSupport h f

end Langlands.Aubert.Support
