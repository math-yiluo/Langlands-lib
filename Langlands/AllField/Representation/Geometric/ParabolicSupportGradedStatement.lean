import Langlands.Representation.Geometric.ParabolicSupportGradedStatement
import Langlands.AllField.Representation.Geometric.ParabolicSupportFiltration
/-! Natural graded identifications for the fixed parabolic support-image filtration. -/

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicSupportGradedTheorem geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

universe uF uV

/-- For any actual orbit ordering by minimal permutation matrices and any
standard intersection refinements, the fixed support-image filtration has
exactly the normalized geometric-piece functors as its natural graded pieces. -/
def PadicParabolicSupportGradedTheorem : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ), 0 < n → ∀ B C : BlockShape n,
    letI := T.topology
    ∀ (m : ℕ) (e : Fin m ≃ MinimalRepresentatives B C)
      (s : OrderedDoubleCosets (B.parabolic F) (C.parabolic F) m),
      (∀ i, s.representative i = permutation n F (e i).val) →
      ∀ (S : MinimalRepresentatives B C → BlockRefinement B)
        (R : MinimalRepresentatives B C → BlockRefinement C)
        (hS : ∀ w, IsIntersectionRefinement (F := F) B C w.val (S w))
        (hR : ∀ w, IsIntersectionRefinement (F := F) C B w.val⁻¹ (R w)),
        (parabolicJacquetSupportFiltration.{uF, uV} T B C s).HasGradedPieces
          (fun i => geometricPieceFunctor T B C (e i).val
            (S (e i)) (R (e i)) (hS (e i)).2.1 (hR (e i)).2.1)

end Langlands.AllField.Geometric
