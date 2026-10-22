import Langlands.Representation.Geometric.ParabolicOrbitJacquet

/-! The local normalized comparison for one actual parabolic double-coset orbit. -/

namespace Langlands.Geometric

open GeneralLinear CategoryTheory

universe uF uV

/-- Normalized radical coinvariants of one actual compact orbit piece agree
naturally with the corresponding normalized geometric-piece functor. -/
def PadicParabolicOrbitJacquetComparison : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B C : BlockShape n,
    letI := T.topology
    ∀ (w : MinimalRepresentatives B C) (S : BlockRefinement B)
      (R : BlockRefinement C)
      (hS : IsIntersectionRefinement (F := F.Carrier) B C w.val S)
      (hR : IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ R),
      Nonempty (parabolicOrbitJacquetFunctor.{uF, uV} T B C w.val ≅
        geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1)

end Langlands.Geometric
