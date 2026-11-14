import Langlands.Representation.Geometric.ParabolicSupportTransport
import Langlands.AllField.Representation.Geometric.ParabolicSupportFiltration
/-! Smooth inducing covariance and transport of the actual support quotients. -/

noncomputable section
open CategoryTheory

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV


end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicSupportGradedCompactSmoothIso
open Langlands.AllField.Geometric

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
universe uF uV

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)

/-- At the same index, compact support with smooth inducing covariance and
actual normalized parabolic smooth induction have naturally isomorphic quotients. -/
def parabolicSupportGradedCompactSmoothIso {m : ℕ}
    (s : letI := T.topology
      OrderedDoubleCosets (B.parabolic F) (C.parabolic F) m)
    (i : Fin m) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    B.smoothInducingFunctor (T.leviHalfCharacter B) ⋙
        (s.supportFiltration.{0, uF, uV} (R := ℂ)).graded i ≅
      (parabolicInductionSupportFiltration.{uF, uV} T B C s).graded i := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI : CompactSpace (Induction.LeftQuotient (B.parabolic F)) :=
    Langlands.AllField.Parabolic.parabolicQuotientCompact F T B
  exact Functor.isoWhiskerLeft (B.inducingFunctor (T.leviHalfCharacter B))
    (s.rawSupportGradedCompactSmoothIso (R := ℂ) i)

end Langlands.AllField.Geometric
