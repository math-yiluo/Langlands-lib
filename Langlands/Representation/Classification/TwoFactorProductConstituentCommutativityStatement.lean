import Langlands.Representation.CuspidalSupport.BlockPermutation
import Langlands.Group.GL.AdjacentMergeShape
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Filtration.ObjectDefinitions

/-!
# Constituent commutativity of a product of two irreducible GL factors

The irreducible two-factor case of Zelevinsky (1980), Theorem 1.9, for the
actual normalized upper induced representations. This is a proposition
definition, not a proof.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For irreducible smooth complex factors `π₁, π₂`, the actual products
`π₁ × π₂` and `π₂ × π₁` have the same composition factors with
multiplicities. The swapped shape puts old block `σ i` at new position `i`. -/
def TwoFactorProductConstituentCommutativity : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n) (h₂ : B.length = 2)
    (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, (A i).IsIrreducible) →
    let σ := B.adjacentSwap 0 (by omega)
    HaveSameJordanHolderFactors
      (Rep.of ((T.normalizedProductInductionFunctor B).obj A).representation)
      (Rep.of ((T.normalizedProductInductionFunctor (B.permute σ)).obj
        (fun i => A (σ i))).representation)

end Langlands.Classification
