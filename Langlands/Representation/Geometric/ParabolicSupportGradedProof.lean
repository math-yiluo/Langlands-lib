import Langlands.Representation.Geometric.ParabolicSupportTransport
import Langlands.Representation.Geometric.ParabolicSupportGradedStatement
import Langlands.Representation.Geometric.ParabolicSupportJacquetProof
import Langlands.Representation.Geometric.ParabolicOrbitJacquetProof
import Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.CountabilityProof

noncomputable section
open CategoryTheory

namespace Langlands.Geometric

open GeneralLinear
universe uF uV

/-- The fixed normalized Jacquet support-image filtration has exactly the
normalized geometric-piece functors as its natural graded pieces. -/
theorem padicParabolicSupportGradedTheorem :
    PadicParabolicSupportGradedTheorem.{uF, uV} := by
  intro p _ F T n hn B C
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearT2Space n
  let := T.generalLinearSigmaCompactSpace n
  intro m e s hs S R hS hR i
  obtain ⟨eJ⟩ := padicParabolicSupportJacquetComparison.{uF, uV} p F T n B C m s i
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
  obtain ⟨eO⟩ := padicParabolicOrbitJacquetComparison.{uF, uV} p F T n hn B C
    (e i) (S (e i)) (R (e i)) (hS (e i)) (hR (e i))
  exact ⟨eJ ≪≫ Functor.isoWhiskerRight eSupport
    (Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C)) ≪≫ eO⟩

end Langlands.Geometric
