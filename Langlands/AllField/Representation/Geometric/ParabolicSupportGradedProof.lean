import Langlands.Representation.Geometric.ParabolicSupportGradedProof
import Langlands.AllField.Representation.Geometric.ParabolicOrbitJacquetProof
import Langlands.AllField.Representation.Geometric.ParabolicSupportGradedStatement
import Langlands.AllField.Representation.Geometric.ParabolicSupportJacquetProof
import Langlands.AllField.Representation.Geometric.ParabolicSupportTransport
noncomputable section
open CategoryTheory

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicOrbitJacquetComparison PadicParabolicSupportGradedTheorem PadicParabolicSupportJacquetComparison PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicParabolicOrbitJacquetComparison padicParabolicSupportGradedTheorem padicParabolicSupportJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor parabolicSupportGradedCompactSmoothIso refinedLeviModulus_of_diagonal supportCoinvariantsImageHom_injective supportCoinvariantsImageIso supportImageNatIso supportImageQuotientHom supportImageQuotientHom_bijective supportImageQuotientIso supportImageToQuotient supportImageToQuotient_ker supportImageToQuotient_on_support supportImageToQuotient_surjective
open Langlands.AllField.Geometric

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
universe uF uV

/-- The fixed normalized Jacquet support-image filtration has exactly the
normalized geometric-piece functors as its natural graded pieces. -/
theorem padicParabolicSupportGradedTheorem :
    PadicParabolicSupportGradedTheorem.{uF, uV} := by
  intro F _ T n hn B C
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
  obtain ⟨eM⟩ := closedSubgroupMackeyFiltration.{uF, uV} (GeneralLinear n F)
    (B.parabolic F) (C.parabolic F)
    (B.isClosed_parabolic F) (C.isClosed_parabolic F) m s i
  have eSupport : (parabolicInductionSupportFiltration.{uF, uV} T B C s).graded i ≅
      B.inducingFunctor (T.leviHalfCharacter B) ⋙
        rawOrbitPiece (B.parabolic F) (C.parabolic F)
          (permutation n F (e i).val) := by
    have ee := (parabolicSupportGradedCompactSmoothIso.{uF, uV} T B C s i).symm ≪≫
      Functor.isoWhiskerLeft (B.smoothInducingFunctor (T.leviHalfCharacter B)) eM
    dsimp only at ee
    rw [orbitPiece_eq_rawOrbitPiece] at ee
    change (parabolicInductionSupportFiltration.{uF, uV} T B C s).graded i ≅
      B.inducingFunctor (T.leviHalfCharacter B) ⋙
        rawOrbitPiece (B.parabolic F) (C.parabolic F)
          (s.representative i) at ee
    simpa only [hs i] using ee
  obtain ⟨eO⟩ := padicParabolicOrbitJacquetComparison.{uF, uV} F T n hn B C
    (e i) (S (e i)) (R (e i)) (hS (e i)) (hR (e i))
  exact ⟨eJ ≪≫ Functor.isoWhiskerRight eSupport
    (Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C)) ≪≫ eO⟩

end Langlands.AllField.Geometric
