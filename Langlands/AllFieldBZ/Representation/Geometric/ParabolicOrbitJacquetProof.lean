import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitCompactComparison
import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitJacquetStatement
import Langlands.Representation.Geometric.ParabolicOrbitJacquetProof

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitJacquetProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicOrbitJacquetProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open CategoryTheory
open Langlands.GeneralLinear hiding SupercuspidalClass blockSum rankInclusion
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicParabolicOrbitJacquetComparison PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicParabolicOrbitJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor refinedLeviModulus_of_diagonal
open Langlands.AllFieldBZ.Geometric
open Langlands.Induction
universe uF uV

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : MinimalRepresentatives B C) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w.val S)
  (hR : IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ R)

/-- The actual orbit integral, target normalization and refined induction form
one natural isomorphism on the full smooth source category. -/
theorem parabolicOrbitJacquetComparison :
    letI := T.topology
    Nonempty (Langlands.AllFieldBZ.Geometric.parabolicOrbitJacquetFunctor.{uF, uV} T B C w.val ≅
      Langlands.AllFieldBZ.Geometric.geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1) := by
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
        (compactInducedMap (parabolicOrbitStabilizer F.Carrier B C w.val)
          (parabolicOrbitCoefficientMap F.Carrier B C w.val (T.leviHalfModulus B)
            (SmoothRep.hom f))) z)) =
    T.normalizedRefinedInducedMap C R
      (refinedIntersectionTransportMap F.Carrier B C w.val S R hS.2.1 hR.2.1
        (T.normalizedRefinedJacquetMap B S (SmoothRep.hom f)))
      (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR A.representation
        (E A z))
  have h₁ := hE A A' f z
  have h₂ := T.parabolicOrbitInductionTransportEquiv_natural B C w S R hS hR
    (SmoothRep.hom f) (E A z)
  exact (congrArg (fun q => T.parabolicOrbitInductionTransportEquiv B C w S R hS hR
    A'.representation q) h₁).trans h₂

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicParabolicOrbitJacquetComparison PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicParabolicOrbitJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor refinedLeviModulus_of_diagonal
universe uF uV

/-- BZ77's local comparison, with all normalizing characters cancelled, for
all supplied actual p-adic data and all smooth complex source representations. -/
theorem padicParabolicOrbitJacquetComparison :
    PadicParabolicOrbitJacquetComparison.{uF, uV} := by
  intro F T n hn B C
  let := T.topology
  intro w S R hS hR
  exact T.parabolicOrbitJacquetComparison B C w S R hS hR

end Langlands.AllFieldBZ.Geometric
