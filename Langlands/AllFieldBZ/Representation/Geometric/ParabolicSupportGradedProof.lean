import Langlands.AllFieldBZ.Group.GL.CountabilityProof
import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitJacquetProof
import Langlands.AllFieldBZ.Representation.Geometric.ParabolicSupportGradedStatement
import Langlands.AllFieldBZ.Representation.Geometric.ParabolicSupportJacquetProof
import Langlands.AllFieldBZ.Representation.Geometric.ParabolicSupportTransport
import Langlands.Representation.Geometric.ParabolicSupportGradedProof

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicSupportGradedProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicSupportGradedProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicParabolicOrbitJacquetComparison PadicParabolicSupportGradedTheorem PadicParabolicSupportJacquetComparison PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicParabolicOrbitJacquetComparison padicParabolicSupportGradedTheorem padicParabolicSupportJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor parabolicSupportGradedCompactSmoothIso refinedLeviModulus_of_diagonal supportCoinvariantsImageHom_injective supportCoinvariantsImageIso supportImageNatIso supportImageQuotientHom supportImageQuotientHom_bijective supportImageQuotientIso supportImageToQuotient supportImageToQuotient_ker supportImageToQuotient_on_support supportImageToQuotient_surjective
open Langlands.GeneralLinear
universe uF uV

/-- The fixed normalized Jacquet support-image filtration has exactly the
normalized geometric-piece functors as its natural graded pieces. -/
theorem padicParabolicSupportGradedTheorem :
    PadicParabolicSupportGradedTheorem.{uF, uV} := by
  intro F T n hn B C
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearT2Space n
  let := T.generalLinearSigmaCompactSpace n
  intro m e s hs S R hS hR i
  obtain ⟨eJ⟩ := padicParabolicSupportJacquetComparison.{uF, uV} F T n B C m s i
  obtain ⟨eM⟩ := closedSubgroupMackeyFiltration.{uF, uV} (GeneralLinear n F.Carrier)
    (B.parabolic F.Carrier) (C.parabolic F.Carrier)
    (B.isClosed_parabolic F.Carrier) (C.isClosed_parabolic F.Carrier) m s i
  have eSupport : (parabolicInductionSupportFiltration.{uF, uV} T B C s).graded i ≅
      B.inducingFunctor (T.leviHalfCharacter B) ⋙
        rawOrbitPiece (B.parabolic F.Carrier) (C.parabolic F.Carrier)
          (permutation n F.Carrier (e i).val) := by
    have ee := (parabolicSupportGradedCompactSmoothIso.{uF, uV} T B C s i).symm ≪≫
      Functor.isoWhiskerLeft (B.smoothInducingFunctor (T.leviHalfCharacter B)) eM
    dsimp only at ee
    rw [orbitPiece_eq_rawOrbitPiece] at ee
    change (parabolicInductionSupportFiltration.{uF, uV} T B C s).graded i ≅
      B.inducingFunctor (T.leviHalfCharacter B) ⋙
        rawOrbitPiece (B.parabolic F.Carrier) (C.parabolic F.Carrier)
          (s.representative i) at ee
    simpa only [hs i] using ee
  obtain ⟨eO⟩ := padicParabolicOrbitJacquetComparison.{uF, uV} F T n hn B C
    (e i) (S (e i)) (R (e i)) (hS (e i)) (hR (e i))
  exact ⟨eJ ≪≫ Functor.isoWhiskerRight eSupport
    (Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C)) ≪≫ eO⟩

end Langlands.AllFieldBZ.Geometric
