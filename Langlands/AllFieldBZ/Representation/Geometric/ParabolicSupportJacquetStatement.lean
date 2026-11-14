import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitJacquet
import Langlands.Representation.Geometric.ParabolicSupportJacquetStatement

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicSupportJacquetStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicSupportJacquetStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicSupportJacquetComparison geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor
open Langlands.GeneralLinear
open CategoryTheory
universe uF uV

/-- The successive quotients of the fixed normalized Jacquet image filtration
are naturally the normalized radical coinvariants of the support quotients. -/
def PadicParabolicSupportJacquetComparison : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) (B C : BlockShape n),
    letI := T.topology
    ∀ (m : ℕ)
      (s : OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m)
      (i : Fin m),
      Nonempty ((parabolicJacquetSupportFiltration.{uF, uV} T B C s).graded i ≅
        (parabolicInductionSupportFiltration.{uF, uV} T B C s).graded i ⋙
          Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C))

end Langlands.AllFieldBZ.Geometric
