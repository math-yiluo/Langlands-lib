import Langlands.Representation.Aubert.CorrectedGradedOrbitComparison

/-! Actual cut comparisons on all corrected graded support classes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open CategoryTheory

namespace Langlands.Aubert.Support

open GeneralLinear Geometric Induction

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
  (B C : BlockShape n) (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))

/-- The genuine quotient cut map takes a supported class to the class of
the actual support-preserving cut map. -/
theorem correctedSupportOrbitClass_cutMap
    (D : BlockShape n) (h : B.cuts ⊆ D.cuts) :
    letI := T.topology
    ∀ f : (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A),
      (cutSupportQuotientMap T A C h (θ \ {w}) θ).hom
          (correctedSupportOrbitClass T A B C θ w f) =
        correctedSupportOrbitClass T A D C θ w
          ⟨Transition.cutMap T A.representation h f.val,
            cutMap_mem_correctedInductionSupport T A C h θ f.val f.property⟩ := by
  intros
  rfl

variable
  (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
  (hLower : ∀ v ∈ θ \ {w}, ∀ z, inversionLength v < inversionLength z → z ∈ θ \ {w})
  (hw : w ∈ weylSupport B C θ)

/-- The actual graded isomorphism uses the same orbital measure family at
every source-increasing shape. -/
def coherentGradedOrbitIntegralIso (hwInc : TypeASolomon.SourceIncreasing B w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    cutSupportQuotient T A C B (θ \ {w}) θ ≅
      Rep.of (twist (Jacquet.inverseHalfCharacter (T.leviModulus C))
        (compactInduced (parabolicOrbitStagesQuotient F.Carrier B C w)
          (parabolicOrbitIntegratedCoefficient F.Carrier B C w (T.leviHalfModulus B)
            (T.normalizedJacquet B A.representation)))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact correctedGradedOrbitIntegralIso T A B C θ w hθ hLower hw
    (T.parabolicOrbitCoherentMeasures C w B hwInc)

/-- Evaluation of the actual coherent graded isomorphism at a target Levi element. -/
def coherentGradedOrbitIntegralValue (hwInc : TypeASolomon.SourceIncreasing B w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    cutSupportQuotient T A C B (θ \ {w}) θ → C.Levi F.Carrier →
      Representation.Coinvariants (cutOrbitNestedCoefficient T A.representation C w B) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro z l
  exact eval (parabolicOrbitStagesQuotient F.Carrier B C w)
    (parabolicOrbitIntegratedCoefficient F.Carrier B C w (T.leviHalfModulus B)
      (T.normalizedJacquet B A.representation))
    (((coherentGradedOrbitIntegralIso T A B C θ w hθ hLower hw hwInc).hom).hom z).val l

/-- The actual coherent graded value on a supported class is the coherent orbit value. -/
theorem coherentGradedOrbitIntegralValue_class (hwInc : TypeASolomon.SourceIncreasing B w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ (f : (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A)) (l : C.Levi F.Carrier),
      coherentGradedOrbitIntegralValue T A B C θ w hθ hLower hw hwInc
          (correctedSupportOrbitClass T A B C θ w f) l =
        coherentCutOrbitIntegralValue T A B C w hwInc
          (Representation.Coinvariants.mk
            ((compactInduced (parabolicOrbitStabilizer F.Carrier B C w)
              (cutOrbitCoefficient T A B C w)).comp
                (C.leviProjection F.Carrier).ker.subtype)
            (correctedOrbitRestriction T A B C θ w hθ hLower hw f)) l := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro f l
  exact correctedGradedOrbitIntegralIso_hom_class_eval T A B C θ w hθ hLower hw
    (T.parabolicOrbitCoherentMeasures C w B hwInc) f l

/-- For every genuine support-quotient vector, the actual cut map corresponds
pointwise to the orbit coefficient map under the coherent graded isomorphisms. -/
theorem coherentGradedOrbitIntegralValue_cutMap
    (D : BlockShape n) (h : B.cuts ⊆ D.cuts)
    (hwB : TypeASolomon.SourceIncreasing B w)
    (hwD : TypeASolomon.SourceIncreasing D w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ (z : cutSupportQuotient T A C B (θ \ {w}) θ) (l : C.Levi F.Carrier),
      coherentGradedOrbitIntegralValue T A D C θ w hθ hLower
          (weylSupport_mono_source_cuts C h θ hw) hwD
          ((cutSupportQuotientMap T A C h (θ \ {w}) θ).hom z) l =
        cutOrbitCoefficientMap T A.representation B D C w h hwB
          (coherentGradedOrbitIntegralValue T A B C θ w hθ hLower hw hwB z l) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro z l
  obtain ⟨f, rfl⟩ := correctedSupportOrbitClass_surjective T A B C θ w z
  rw [correctedSupportOrbitClass_cutMap]
  let fD : (correctedInductionSupport T D C θ).representation
      ((T.normalizedJacquetFunctor D).obj A) :=
    ⟨Transition.cutMap T A.representation h f.val,
      cutMap_mem_correctedInductionSupport T A C h θ f.val f.property⟩
  have hD := coherentGradedOrbitIntegralValue_class T A D C θ w hθ hLower
    (weylSupport_mono_source_cuts C h θ hw) hwD fD l
  have hB := coherentGradedOrbitIntegralValue_class T A B C θ w hθ hLower hw hwB f l
  have hI := correctedOrbitRestriction_coherent_comparison_cutMap T A B C w D h hwB hwD
    θ hθ hLower hw f l
  exact hD.trans (hI.trans
    (congrArg (cutOrbitCoefficientMap T A.representation B D C w h hwB) hB.symm))

end Langlands.Aubert.Support
