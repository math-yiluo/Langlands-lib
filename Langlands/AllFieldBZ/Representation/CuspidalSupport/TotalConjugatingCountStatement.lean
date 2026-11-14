import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding TotalConjugatingCountTheorem
open Langlands.GeneralLinear
universe uF

/-- Over every finite p-adic extension and every rank, including zero, the
minimal permutations conjugating the actual source Levi onto an actual
standard Levi, taken over all ordered target block shapes, form a finite
set whose cardinality is the factorial of the source block count. -/
def TotalConjugatingCountTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (n : ℕ) (B : BlockShape n),
    Finite ((C : BlockShape n) × MinimalConjugatingPermutations (F := F.Carrier) B C) ∧
      Nat.card ((C : BlockShape n) × MinimalConjugatingPermutations (F := F.Carrier) B C) =
        Nat.factorial B.length

end Langlands.AllFieldBZ.CuspidalSupport
