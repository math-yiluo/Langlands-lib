import Langlands.AllFieldBZ.Representation.Geometric.ParabolicSupportFiltration
import Langlands.AllFieldBZ.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Geometric.ParabolicSupportTransport

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicSupportTransport`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicSupportTransport` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicSupportGradedCompactSmoothIso
open Langlands.GeneralLinear
universe uF uV

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- At the same index, compact support with smooth inducing covariance and
actual normalized parabolic smooth induction have naturally isomorphic quotients. -/
def parabolicSupportGradedCompactSmoothIso {m : ℕ}
    (s : letI := T.topology
      OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m)
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
  letI : CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier)) :=
    Parabolic.parabolicQuotientCompact F T B
  exact Functor.isoWhiskerLeft (B.inducingFunctor (T.leviHalfCharacter B))
    (s.rawSupportGradedCompactSmoothIso (R := ℂ) i)

end Langlands.AllFieldBZ.Geometric
