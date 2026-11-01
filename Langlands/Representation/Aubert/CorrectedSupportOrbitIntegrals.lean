import Langlands.Representation.Aubert.CorrectedOrbitCutIntegrals

/-! Orbital integrals of actual corrected-support representatives. -/

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
  (B C : BlockShape n) (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
  (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
  (hLower : ∀ v ∈ θ \ {w}, ∀ z, inversionLength v < inversionLength z → z ∈ θ \ {w})
  (hw : w ∈ weylSupport B C θ)

/-- The actual compact orbit restriction of a corrected induction-support
representative, through the canonical support quotient projection. -/
def correctedOrbitRestriction :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A) →
      CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
        (cutOrbitCoefficient T A B C w) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro f
  exact ((correctedInductionOrbitIso T B C θ w hθ hLower hw).hom.app
    ((T.normalizedJacquetFunctor B).obj A)).hom
      (((correctedInductionSupport T B C (θ \ {w})).quotientProjection
        (correctedInductionSupport T B C θ)
        ((T.normalizedJacquetFunctor B).obj A)).hom f)

@[simp]
theorem correctedOrbitRestriction_eval :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (f : (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A))
      (q : C.parabolic F.Carrier),
      eval _ _ (correctedOrbitRestriction T A B C θ w hθ hLower hw f).val q =
        eval _ _ f.val ((permutation n F.Carrier w)⁻¹ *
          (q : GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro f q
  exact correctedInductionOrbitIso_hom_projection_eval T B C θ w hθ hLower hw
    ((T.normalizedJacquetFunctor B).obj A) f q

variable {D : BlockShape n} (h : B.cuts ⊆ D.cuts)

/-- The actual cut map sends corrected orbit restrictions to their pointwise
Jacquet quotient projections. -/
theorem correctedOrbitRestriction_cutMap_eval :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (f : (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A))
      (q : C.parabolic F.Carrier),
      let fD : (correctedInductionSupport T D C θ).representation
          ((T.normalizedJacquetFunctor D).obj A) :=
        ⟨Transition.cutMap T A.representation h f.val,
          cutMap_mem_correctedInductionSupport T A C h θ f.val f.property⟩
      eval _ _ (correctedOrbitRestriction T A D C θ w hθ hLower
          (weylSupport_mono_source_cuts C h θ hw) fD).val q =
        Transition.quotient A.representation
          (unipotentSubgroup_le_of_cuts_subset h)
          (eval _ _ (correctedOrbitRestriction T A B C θ w hθ hLower hw f).val q) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact correctedInductionOrbit_cutMap_projection_eval T A C θ w hθ hLower hw h

/-- For the actual support representatives, the stages integral square needs
no additional pointwise-compatibility premise. It uses one quotient measure
and its pushforward along the actual cut-coordinate homeomorphism. -/
theorem correctedOrbitRestriction_integral_cutMap (hwInc : TypeASolomon.SourceIncreasing B w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace (QuotientIntegration.LeftQuotient
      (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
    letI : MeasurableSpace (QuotientIntegration.LeftQuotient
      (parabolicOrbitNestedIntersection F.Carrier D C w)) := borel _
    ∀ (ν : Measure (QuotientIntegration.LeftQuotient
        (parabolicOrbitNestedIntersection F.Carrier B C w)))
      [IsFiniteMeasureOnCompacts ν]
      (f : (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A))
      (l : C.Levi F.Carrier),
      let fD : (correctedInductionSupport T D C θ).representation
          ((T.normalizedJacquetFunctor D).obj A) :=
        ⟨Transition.cutMap T A.representation h f.val,
          cutMap_mem_correctedInductionSupport T A C h θ f.val f.property⟩
      AlgebraicIntegral.integral
          (Measure.map (parabolicOrbitNestedQuotientCutHomeomorph F.Carrier B D C w h hwInc) ν)
          (cutOrbitIntegrand T A D C w
            (correctedOrbitRestriction T A D C θ w hθ hLower
              (weylSupport_mono_source_cuts C h θ hw) fD) l) =
        cutOrbitCoefficientMap T A.representation B D C w h hwInc
          (AlgebraicIntegral.integral ν
            (cutOrbitIntegrand T A B C w
              (correctedOrbitRestriction T A B C θ w hθ hLower hw f) l)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier D C w)) := borel _
  intro ν hν f l
  apply cutOrbitStagesIntegral_map T A B D C w h hwInc ν
  exact correctedOrbitRestriction_cutMap_eval T A B C θ w hθ hLower hw h f

end Langlands.Aubert.Support
