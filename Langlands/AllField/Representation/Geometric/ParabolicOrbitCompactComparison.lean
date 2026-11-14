import Langlands.Representation.Geometric.ParabolicOrbitCompactComparison
import Langlands.AllField.Representation.Geometric.ParabolicOrbitInductionTransport
import Langlands.AllField.Representation.Geometric.ParabolicOrbitJacquet
import Langlands.AllField.Representation.Geometric.ParabolicOrbitMeasureData
/-! Specialization of the actual relative integral to the parabolic orbit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor refinedLeviModulus_of_diagonal
open Langlands.AllField.Geometric

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Induction hiding SmoothRep

universe uF uV uW


end Langlands.AllField.Geometric

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open _root_.MeasureTheory MeasureTheory.Measure _root_.CategoryTheory
open Langlands.GeneralLinear hiding SupercuspidalClass blockSum rankInclusion
open Langlands.AllField.GeneralLinear
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor refinedLeviModulus_of_diagonal
open Langlands.AllField.Geometric
open Langlands.Induction hiding SmoothRep
open Langlands.QuotientIntegration

universe uF uV

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n))

/-- One choice of actual quotient measures supplies a natural family of the
unnormalized compact orbit integral equivalences. -/
theorem parabolicOrbitCompactComparison_exists :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∃ E : ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
      (Parabolic.leviCoinvariants C
        (compactInduced (parabolicOrbitStabilizer F B C w)
          (parabolicOrbitCoefficient F B C w (T.leviHalfModulus B)
            A.representation))).Equiv
        (compactInduced (parabolicOrbitStagesQuotient F B C w)
          (parabolicOrbitIntegratedCoefficient F B C w (T.leviHalfModulus B)
            A.representation)),
      ∀ (A A' : SmoothRep.{0, uF, uV} ℂ (B.Levi F)) (f : A ⟶ A') z,
        E A' (Parabolic.leviCoinvariantsMap C
            (compactInducedMap (parabolicOrbitStabilizer F B C w)
              (parabolicOrbitCoefficientMap F B C w (T.leviHalfModulus B)
                (SmoothRep.hom f))) z) =
          compactInducedMap (parabolicOrbitStagesQuotient F B C w)
            (parabolicOrbitIntegratedCoefficientMap F B C w
              (T.leviHalfModulus B) (SmoothRep.hom f))
            (E A z) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.parabolicLocallyCompactSpace C
  let N := (parabolicOrbitStagesRetraction F B C w).ker
  let I := parabolicOrbitNestedIntersection F B C w
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace I := borel I
  let : BorelSpace I := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient I) := borel (QuotientIntegration.LeftQuotient I)
  let : BorelSpace (QuotientIntegration.LeftQuotient I) := ⟨rfl⟩
  let := T.unipotentRadicalLocallyCompactSpace C
  let : LocallyCompactSpace N :=
    (parabolicOrbitNestedRadicalEquiv F B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hm := T.parabolicOrbitNested_measureExists B C w
  dsimp only at hm
  obtain ⟨μN, μI, hμN, hμNr, hμNri, hμI, hμIr, hμIri, ν, hν, hc⟩ := hm
  let := hμN
  let := hμNr
  let := hμNri
  let := hμI
  let := hμIr
  let := hμIri
  let := hν
  have hσ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F)) :
      IsSmooth (parabolicOrbitCoefficient F B C w (T.leviHalfModulus B)
        A.representation) :=
    isSmooth_comp (parabolicOrbitToSourceLevi F B C w)
      (continuous_parabolicOrbitToSourceLevi F B C w)
      ((isSmooth_twist_iff (T.leviHalfModulus B) A.representation
        (T.isOpen_ker_leviHalfModulus B)).mpr A.isSmooth)
  have hN : IsClosed ((C.leviProjection F).ker :
      Set (C.parabolic F)) :=
    isClosed_singleton.preimage (C.leviProjectionContinuous F).continuous
  let E := fun A : SmoothRep.{0, uF, uV} ℂ (B.Levi F) =>
    splitStagesCompactEquiv
      (C.leviProjection F) (C.leviInParabolic F)
      (C.leviProjection_section F)
      (C.leviProjectionContinuous F).continuous
      (C.leviInParabolicContinuous F).continuous
      (parabolicOrbitStages F B C w)
      (parabolicOrbitStabilizer F B C w)
      (parabolicOrbitStages_kernel_le F B C w)
      (parabolicOrbitStabilizer_le_stages F B C w)
      (isClosed_parabolicOrbitStages F B C w)
      (isClosed_parabolicOrbitStabilizer F B C w)
      (parabolicOrbitStages_section_mem F B C w)
      (parabolicOrbitCoefficient F B C w (T.leviHalfModulus B) A.representation)
      (hσ A) ν (T.parabolicOrbitNestedKernel_compactOpenBasis B C w) μN μI hc hN
      (T.parabolicOrbitParabolic_compactOpenBasis C)
  let E' := fun A : SmoothRep.{0, uF, uV} ℂ (B.Levi F) =>
    (E A).trans (compactInducedEquiv (parabolicOrbitStagesQuotient F B C w)
      (parabolicOrbitIntegratedCoefficientEquiv F B C w (T.leviHalfModulus B)
        A.representation))
  refine ⟨E', ?_⟩
  intro A A' f z
  have hn := splitStagesCompactEquiv_natural
    (C.leviProjection F) (C.leviInParabolic F)
    (C.leviProjection_section F)
    (C.leviProjectionContinuous F).continuous
    (C.leviInParabolicContinuous F).continuous
    (parabolicOrbitStages F B C w)
    (parabolicOrbitStabilizer F B C w)
    (parabolicOrbitStages_kernel_le F B C w)
    (parabolicOrbitStabilizer_le_stages F B C w)
    (isClosed_parabolicOrbitStages F B C w)
    (isClosed_parabolicOrbitStabilizer F B C w)
    (parabolicOrbitStages_section_mem F B C w)
    (parabolicOrbitCoefficient F B C w (T.leviHalfModulus B) A.representation)
    (hσ A) ν (T.parabolicOrbitNestedKernel_compactOpenBasis B C w) μN μI hc
    (hσ A') (parabolicOrbitCoefficientMap F B C w (T.leviHalfModulus B)
      (SmoothRep.hom f)) hN (T.parabolicOrbitParabolic_compactOpenBasis C) z
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext l
  have he := congrArg (fun q : CompactFunctions
      (parabolicOrbitStagesQuotient F B C w)
      (twist (Jacquet.complexCharacter
        (splitKernelHaarRatio (parabolicOrbitStagesRetraction F B C w)
          ((C.leviInParabolic F).subgroupComap (parabolicOrbitStages F B C w))
          (parabolicOrbitNestedStabilizer F B C w)
          (parabolicOrbitNestedSection_mem F B C w)
          ((isClosed_parabolicOrbitStabilizer F B C w).preimage continuous_subtype_val)))
        (parabolicOrbitNestedCoefficientAction F B C w (T.leviHalfModulus B)
          A'.representation)) => q.val.val.val l) hn
  exact he

end Langlands.LocalFieldData
