import Langlands.Representation.CuspidalSupport.LeviDefinitions

/-! BZ77 2.8: the total number of minimal conjugating block permutations. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF

/-- Over every finite p-adic extension and every rank, including zero, the
minimal permutations conjugating the actual source Levi onto an actual
standard Levi, taken over all ordered target block shapes, form a finite
set whose cardinality is the factorial of the source block count. -/
def TotalConjugatingCountTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ) (B : BlockShape n),
    Finite ((C : BlockShape n) × MinimalConjugatingPermutations (F := F.Carrier) B C) ∧
      Nat.card ((C : BlockShape n) × MinimalConjugatingPermutations (F := F.Carrier) B C) =
        Nat.factorial B.length

end Langlands.CuspidalSupport
