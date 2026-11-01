import Langlands.Representation.Aubert.CorrectedOrbitCoherentComparison

/-! Actual support-quotient comparison with normalized orbit coefficients. -/

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

/-- The actual class of a supported induction vector in the quotient of
the corrected Jacquet images. -/
def correctedSupportOrbitClass :
    letI := T.topology
    (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A) →
      cutSupportQuotient T A C B (θ \ {w}) θ := by
  let := T.topology
  intro f
  exact ((correctedJacquetSupport T B C (θ \ {w})).quotientProjection
    (correctedJacquetSupport T B C θ) ((T.normalizedJacquetFunctor B).obj A)).hom
      ⟨C.jacquetMk (cutTermObject T A B).representation f.val,
        f.val, f.property, rfl⟩

theorem correctedSupportOrbitClass_surjective :
    letI := T.topology
    Function.Surjective (correctedSupportOrbitClass T A B C θ w) := by
  let := T.topology
  intro z
  obtain ⟨q, rfl⟩ := (correctedJacquetSupport T B C (θ \ {w})).quotientProjection_surjective
    (correctedJacquetSupport T B C θ) ((T.normalizedJacquetFunctor B).obj A) z
  obtain ⟨f, hf, he⟩ := q.property
  refine ⟨⟨f, hf⟩, ?_⟩
  apply congrArg
    (((correctedJacquetSupport T B C (θ \ {w})).quotientProjection
      (correctedJacquetSupport T B C θ) ((T.normalizedJacquetFunctor B).obj A)).hom)
  exact Subtype.ext he

variable
  (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
  (hLower : ∀ v ∈ θ \ {w}, ∀ z, inversionLength v < inversionLength z → z ∈ θ \ {w})
  (hw : w ∈ weylSupport B C θ)

/-- The canonical support-image quotient comparison followed by the actual
orbit restriction takes a supported class to its genuine radical class. -/
theorem correctedJacquetOrbitIso_hom_class :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ f : (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A),
      ((correctedJacquetOrbitIso T B C θ w hθ hLower hw).hom.app
          ((T.normalizedJacquetFunctor B).obj A)).hom
          (correctedSupportOrbitClass T A B C θ w f) =
        Representation.Coinvariants.mk
          ((compactInduced (parabolicOrbitStabilizer F.Carrier B C w)
            (cutOrbitCoefficient T A B C w)).comp
              (C.leviProjection F.Carrier).ker.subtype)
          (correctedOrbitRestriction T A B C θ w hθ hLower hw f) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro f
  have hi := supportImageToQuotient_on_support T B C
    (correctedInductionSupport T B C (θ \ {w}))
    (correctedInductionSupport T B C θ) ((T.normalizedJacquetFunctor B).obj A) f
  exact congrArg
    (((Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C)).map
      ((correctedInductionOrbitIso T B C θ w hθ hLower hw).hom.app
        ((T.normalizedJacquetFunctor B).obj A))).hom) hi

/-- The actual graded support quotient is the compact orbit coefficient,
including the target inverse half-modulus twist. -/
def correctedGradedOrbitIntegralIso
    (m : letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      ParabolicOrbitIntegralMeasures F.Carrier B C w) :
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
  exact (correctedJacquetOrbitIso T B C θ w hθ hLower hw).app
      ((T.normalizedJacquetFunctor B).obj A) ≪≫
    Rep.mkIso (twistEquiv (Jacquet.inverseHalfCharacter (T.leviModulus C))
      (T.parabolicOrbitCompactIntegralEquiv B C w m
        ((T.normalizedJacquetFunctor B).obj A)))

/-- Evaluation of the actual graded isomorphism on a supported class uses
the already compared actual orbit integral. -/
theorem correctedGradedOrbitIntegralIso_hom_class_eval :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ (m : ParabolicOrbitIntegralMeasures F.Carrier B C w)
      (f : (correctedInductionSupport T B C θ).representation
        ((T.normalizedJacquetFunctor B).obj A)) (l : C.Levi F.Carrier),
      eval _ _
          (((correctedGradedOrbitIntegralIso T A B C θ w hθ hLower hw m).hom).hom
            (correctedSupportOrbitClass T A B C θ w f)).val l =
        cutOrbitIntegralValue T A B C w m
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
  intro m f l
  exact congrArg
    (fun z => cutOrbitIntegralValue T A B C w m z l)
    (correctedJacquetOrbitIso_hom_class T A B C θ w hθ hLower hw f)

end Langlands.Aubert.Support
