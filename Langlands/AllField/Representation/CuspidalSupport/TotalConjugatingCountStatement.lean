import Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement
import Langlands.AllField.Group.GL.PadicSupplement
/-! BZ77 2.8: the total number of minimal conjugating block permutations. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding TotalConjugatingCountTheorem
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF

/-- Over every finite p-adic extension and every rank, including zero, the
minimal permutations conjugating the actual source Levi onto an actual
standard Levi, taken over all ordered target block shapes, form a finite
set whose cardinality is the factorial of the source block count. -/
def TotalConjugatingCountTheorem : Prop :=
  ∀ (F : Type uF) [Field F] (n : ℕ) (B : BlockShape n),
    Finite ((C : BlockShape n) × MinimalConjugatingPermutations (F := F) B C) ∧
      Nat.card ((C : BlockShape n) × MinimalConjugatingPermutations (F := F) B C) =
        Nat.factorial B.length

end Langlands.AllField.CuspidalSupport
