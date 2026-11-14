import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitInductionTransport
import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitJacquet
import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitMeasureData
import Langlands.AllFieldBZ.Representation.Induction.SplitStagesComparison
import Langlands.Representation.Geometric.ParabolicOrbitCompactComparison

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitCompactComparison`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicOrbitCompactComparison` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor refinedLeviModulus_of_diagonal
open Langlands.GeneralLinear
open Langlands.Induction
open MeasureTheory
universe uF uV uW

variable (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  [T2Space F] {n : ℕ} [LocallyCompactSpace (GeneralLinear n F)]
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

local instance : LocallyCompactSpace (C.unipotentSubgroup F) :=
  (C.isClosed_unipotentSubgroup F).locallyCompactSpace
local instance : LocallyCompactSpace (parabolicOrbitStagesRetraction F B C w).ker :=
  (parabolicOrbitNestedKernelAmbientEquiv F B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance : MeasurableSpace (parabolicOrbitStagesRetraction F B C w).ker :=
  borel _
local instance : BorelSpace (parabolicOrbitStagesRetraction F B C w).ker := ⟨rfl⟩
local instance : MeasurableSpace (parabolicOrbitNestedIntersection F B C w) := borel _
local instance : BorelSpace (parabolicOrbitNestedIntersection F B C w) := ⟨rfl⟩

end Langlands.AllFieldBZ.Geometric
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding SupercuspidalClass blockSum rankInclusion
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor refinedLeviModulus_of_diagonal
open Langlands.AllFieldBZ.Geometric
open Langlands.Induction
open MeasureTheory
open MeasureTheory.Measure
open CategoryTheory
open Langlands.QuotientIntegration
universe uF uV

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n))

/-- One choice of actual quotient measures supplies a natural family of the
unnormalized compact orbit integral equivalences. -/
theorem parabolicOrbitCompactComparison_exists :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∃ E : ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      (Parabolic.leviCoinvariants C
        (compactInduced (parabolicOrbitStabilizer F.Carrier B C w)
          (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B)
            A.representation))).Equiv
        (compactInduced (parabolicOrbitStagesQuotient F.Carrier B C w)
          (parabolicOrbitIntegratedCoefficient F.Carrier B C w (T.leviHalfModulus B)
            A.representation)),
      ∀ (A A' : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) (f : A ⟶ A') z,
        E A' (Parabolic.leviCoinvariantsMap C
            (compactInducedMap (parabolicOrbitStabilizer F.Carrier B C w)
              (parabolicOrbitCoefficientMap F.Carrier B C w (T.leviHalfModulus B)
                (SmoothRep.hom f))) z) =
          compactInducedMap (parabolicOrbitStagesQuotient F.Carrier B C w)
            (parabolicOrbitIntegratedCoefficientMap F.Carrier B C w
              (T.leviHalfModulus B) (SmoothRep.hom f))
            (E A z) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.parabolicLocallyCompactSpace C
  let N := (parabolicOrbitStagesRetraction F.Carrier B C w).ker
  let I := parabolicOrbitNestedIntersection F.Carrier B C w
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace I := borel I
  let : BorelSpace I := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient I) := borel (QuotientIntegration.LeftQuotient I)
  let : BorelSpace (QuotientIntegration.LeftQuotient I) := ⟨rfl⟩
  let := T.unipotentRadicalLocallyCompactSpace C
  let : LocallyCompactSpace N :=
    (parabolicOrbitNestedRadicalEquiv F.Carrier B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace
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
  have hσ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) :
      IsSmooth (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B)
        A.representation) :=
    isSmooth_comp (parabolicOrbitToSourceLevi F.Carrier B C w)
      (continuous_parabolicOrbitToSourceLevi F.Carrier B C w)
      ((isSmooth_twist_iff (T.leviHalfModulus B) A.representation
        (T.isOpen_ker_leviHalfModulus B)).mpr A.isSmooth)
  have hN : IsClosed ((C.leviProjection F.Carrier).ker :
      Set (C.parabolic F.Carrier)) :=
    isClosed_singleton.preimage (C.leviProjectionContinuous F.Carrier).continuous
  let E := fun A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) =>
    splitStagesCompactEquiv
      (C.leviProjection F.Carrier) (C.leviInParabolic F.Carrier)
      (C.leviProjection_section F.Carrier)
      (C.leviProjectionContinuous F.Carrier).continuous
      (C.leviInParabolicContinuous F.Carrier).continuous
      (parabolicOrbitStages F.Carrier B C w)
      (parabolicOrbitStabilizer F.Carrier B C w)
      (parabolicOrbitStages_kernel_le F.Carrier B C w)
      (parabolicOrbitStabilizer_le_stages F.Carrier B C w)
      (isClosed_parabolicOrbitStages F.Carrier B C w)
      (isClosed_parabolicOrbitStabilizer F.Carrier B C w)
      (parabolicOrbitStages_section_mem F.Carrier B C w)
      (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) A.representation)
      (hσ A) ν (T.parabolicOrbitNestedKernel_compactOpenBasis B C w) μN μI hc hN
      (T.parabolicOrbitParabolic_compactOpenBasis C)
  let E' := fun A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) =>
    (E A).trans (compactInducedEquiv (parabolicOrbitStagesQuotient F.Carrier B C w)
      (parabolicOrbitIntegratedCoefficientEquiv F.Carrier B C w (T.leviHalfModulus B)
        A.representation))
  refine ⟨E', ?_⟩
  intro A A' f z
  have hn := splitStagesCompactEquiv_natural
    (C.leviProjection F.Carrier) (C.leviInParabolic F.Carrier)
    (C.leviProjection_section F.Carrier)
    (C.leviProjectionContinuous F.Carrier).continuous
    (C.leviInParabolicContinuous F.Carrier).continuous
    (parabolicOrbitStages F.Carrier B C w)
    (parabolicOrbitStabilizer F.Carrier B C w)
    (parabolicOrbitStages_kernel_le F.Carrier B C w)
    (parabolicOrbitStabilizer_le_stages F.Carrier B C w)
    (isClosed_parabolicOrbitStages F.Carrier B C w)
    (isClosed_parabolicOrbitStabilizer F.Carrier B C w)
    (parabolicOrbitStages_section_mem F.Carrier B C w)
    (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) A.representation)
    (hσ A) ν (T.parabolicOrbitNestedKernel_compactOpenBasis B C w) μN μI hc
    (hσ A') (parabolicOrbitCoefficientMap F.Carrier B C w (T.leviHalfModulus B)
      (SmoothRep.hom f)) hN (T.parabolicOrbitParabolic_compactOpenBasis C) z
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext l
  have he := congrArg (fun q : CompactFunctions
      (parabolicOrbitStagesQuotient F.Carrier B C w)
      (twist (Jacquet.complexCharacter
        (splitKernelHaarRatio (parabolicOrbitStagesRetraction F.Carrier B C w)
          ((C.leviInParabolic F.Carrier).subgroupComap (parabolicOrbitStages F.Carrier B C w))
          (parabolicOrbitNestedStabilizer F.Carrier B C w)
          (parabolicOrbitNestedSection_mem F.Carrier B C w)
          ((isClosed_parabolicOrbitStabilizer F.Carrier B C w).preimage continuous_subtype_val)))
        (parabolicOrbitNestedCoefficientAction F.Carrier B C w (T.leviHalfModulus B)
          A'.representation)) => q.val.val.val l) hn
  exact he

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
