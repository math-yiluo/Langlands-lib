import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitJacquet
import Langlands.Representation.Geometric.ParabolicOrbitJacquetStatement

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitJacquetStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicOrbitJacquetStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicOrbitJacquetComparison geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor
open Langlands.GeneralLinear
open CategoryTheory
universe uF uV

/-- Normalized radical coinvariants of one actual compact orbit piece agree
naturally with the corresponding normalized geometric-piece functor. -/
def PadicParabolicOrbitJacquetComparison : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B C : BlockShape n,
    letI := T.topology
    ∀ (w : MinimalRepresentatives B C) (S : BlockRefinement B)
      (R : BlockRefinement C)
      (hS : IsIntersectionRefinement (F := F.Carrier) B C w.val S)
      (hR : IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ R),
      Nonempty (parabolicOrbitJacquetFunctor.{uF, uV} T B C w.val ≅
        geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1)

end Langlands.AllFieldBZ.Geometric
