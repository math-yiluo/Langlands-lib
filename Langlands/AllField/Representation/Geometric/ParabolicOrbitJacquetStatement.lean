import Langlands.Representation.Geometric.ParabolicOrbitJacquetStatement
import Langlands.AllField.Representation.Geometric.ParabolicOrbitJacquet
/-! The local normalized comparison for one actual parabolic double-coset orbit. -/

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicOrbitJacquetComparison geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor
open Langlands.AllField.Geometric

open _root_.CategoryTheory
open Langlands.GeneralLinear

universe uF uV

/-- Normalized radical coinvariants of one actual compact orbit piece agree
naturally with the corresponding normalized geometric-piece functor. -/
def PadicParabolicOrbitJacquetComparison : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ), 0 < n → ∀ B C : BlockShape n,
    letI := T.topology
    ∀ (w : MinimalRepresentatives B C) (S : BlockRefinement B)
      (R : BlockRefinement C)
      (hS : IsIntersectionRefinement (F := F) B C w.val S)
      (hR : IsIntersectionRefinement (F := F) C B w.val⁻¹ R),
      Nonempty (parabolicOrbitJacquetFunctor.{uF, uV} T B C w.val ≅
        geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1)

end Langlands.AllField.Geometric
