import Langlands.Representation.Geometric.ParabolicOrbitJacquetProof
import Langlands.AllField.Representation.Geometric.ParabolicOrbitCompactComparison
import Langlands.AllField.Representation.Geometric.ParabolicOrbitJacquetStatement
/-! The natural normalized comparison for the actual parabolic orbit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open _root_.CategoryTheory
open Langlands.GeneralLinear hiding SupercuspidalClass blockSum rankInclusion
open Langlands.AllField.GeneralLinear
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicOrbitJacquetComparison PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicParabolicOrbitJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor refinedLeviModulus_of_diagonal
open Langlands.AllField.Geometric
open Langlands.Induction hiding SmoothRep

universe uF uV

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)
  (w : MinimalRepresentatives B C) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F) B C w.val S)
  (hR : IsIntersectionRefinement (F := F) C B w.val⁻¹ R)

/-- The actual orbit integral, target normalization and refined induction form
one natural isomorphism on the full smooth source category. -/
theorem parabolicOrbitJacquetComparison :
    letI := T.topology
    Nonempty (parabolicOrbitJacquetFunctor.{uF, uV} T B C w.val ≅
      geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  have hE := T.parabolicOrbitCompactComparison_exists.{uF, uV} B C w.val
  obtain ⟨E, hE⟩ := hE
  rw [T.geometricPieceFunctor_eq_pullback B C w S R hS hR]
  refine ⟨NatIso.ofComponents (fun A => Rep.mkIso
    ((twistEquiv (Jacquet.inverseHalfCharacter (T.leviModulus C)) (E A)).trans
      (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR A.representation))) ?_⟩
  intro A A' f
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change T.parabolicOrbitInductionTransportEquiv B C w S R hS hR A'.representation
      (E A' (Parabolic.leviCoinvariantsMap C
        (compactInducedMap (parabolicOrbitStabilizer F B C w.val)
          (parabolicOrbitCoefficientMap F B C w.val (T.leviHalfModulus B)
            (SmoothRep.hom f))) z)) =
    T.normalizedRefinedInducedMap C R
      (refinedIntersectionTransportMap F B C w.val S R hS.2.1 hR.2.1
        (T.normalizedRefinedJacquetMap B S (SmoothRep.hom f)))
      (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR A.representation
        (E A z))
  have h₁ := hE A A' f z
  have h₂ := T.parabolicOrbitInductionTransportEquiv_natural B C w S R hS hR
    (SmoothRep.hom f) (E A z)
  exact (congrArg (fun q => T.parabolicOrbitInductionTransportEquiv B C w S R hS hR
    A'.representation q) h₁).trans h₂

end Langlands.LocalFieldData

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicOrbitJacquetComparison PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicParabolicOrbitJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor refinedLeviModulus_of_diagonal
open Langlands.AllField.Geometric

universe uF uV

/-- BZ77's local comparison, with all normalizing characters cancelled, for
all supplied actual p-adic data and all smooth complex source representations. -/
theorem padicParabolicOrbitJacquetComparison :
    PadicParabolicOrbitJacquetComparison.{uF, uV} := by
  intro F _ T n hn B C
  let := T.topology
  intro w S R hS hR
  exact T.parabolicOrbitJacquetComparison B C w S R hS hR

end Langlands.AllField.Geometric
