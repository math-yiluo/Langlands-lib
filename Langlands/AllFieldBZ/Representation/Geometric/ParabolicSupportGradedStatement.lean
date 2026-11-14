import Langlands.AllFieldBZ.Representation.Geometric.ParabolicSupportFiltration
import Langlands.Representation.Geometric.ParabolicSupportGradedStatement

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicSupportGradedStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicSupportGradedStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicSupportGradedTheorem geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration
open Langlands.GeneralLinear
universe uF uV

/-- For any actual orbit ordering by minimal permutation matrices and any
standard intersection refinements, the fixed support-image filtration has
exactly the normalized geometric-piece functors as its natural graded pieces. -/
def PadicParabolicSupportGradedTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B C : BlockShape n,
    letI := T.topology
    ∀ (m : ℕ) (e : Fin m ≃ MinimalRepresentatives B C)
      (s : OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m),
      (∀ i, s.representative i = permutation n F.Carrier (e i).val) →
      ∀ (S : MinimalRepresentatives B C → BlockRefinement B)
        (R : MinimalRepresentatives B C → BlockRefinement C)
        (hS : ∀ w, IsIntersectionRefinement (F := F.Carrier) B C w.val (S w))
        (hR : ∀ w, IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ (R w)),
        (parabolicJacquetSupportFiltration.{uF, uV} T B C s).HasGradedPieces
          (fun i => geometricPieceFunctor T B C (e i).val
            (S (e i)) (R (e i)) (hS (e i)).2.1 (hR (e i)).2.1)

end Langlands.AllFieldBZ.Geometric
