import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Derivative.Iteration

/-! Actual commutation of an irreducible binary normalized product. -/

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For positive, possibly unequal ranks, an irreducible normalized product of
irreducible factors is isomorphic to the reversed product after the literal
entry-preserving total-rank cast. This definition asserts only a proposition. -/
def IrreducibleBinaryProductCommutation : Prop :=
  letI := T.topology
  ∀ (a b : ℕ), 0 < a → 0 < b →
    ∀ (α : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (β : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
      α.IsIrreducible → β.IsIrreducible →
      ((T.binaryNormalizedProductFunctor a b).obj (α, β)).IsIrreducible →
      Nonempty ((T.binaryNormalizedProductFunctor a b).obj (α, β) ≅
        (Derivative.generalLinearRankCast T (Nat.add_comm b a)).obj
          ((T.binaryNormalizedProductFunctor b a).obj (β, α)))

end Langlands.Classification
