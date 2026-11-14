import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.CuspidalSupport.TotalConjugatingCountStatement
import Langlands.AllField.Representation.Geometric.WeylStatementSupplement
/-! BZ77 2.8: proof that the total count of minimal conjugating block
permutations is the factorial of the source block count. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem NonassociatedJacquetSubquotientsTheorem TotalConjugatingCountTheorem totalConjugatingCount
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

universe uF

namespace TotalConjugatingCount
open Langlands.CuspidalSupport.TotalConjugatingCount
open Langlands.AllField.CuspidalSupport.TotalConjugatingCount
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem NonassociatedJacquetSubquotientsTheorem TotalConjugatingCountTheorem totalConjugatingCount
open Langlands.AllField.CuspidalSupport

variable {n : ℕ}

section Blocks

end Blocks

section Matrices


end Matrices

section Conjugation



end Conjugation

section Reordering


end Reordering

section Count


end Count

end TotalConjugatingCount

/-- BZ77 2.8, `l(M) = r!`: over every finite p-adic extension and every rank,
the minimal permutations conjugating a standard Levi onto some standard Levi
are counted, over all target shapes, by the factorial of the block count. -/
theorem totalConjugatingCount : TotalConjugatingCountTheorem.{uF} := by
  intro F _ n B
  exact TotalConjugatingCount.finite_and_card_eq (F := F) B

end Langlands.AllField.CuspidalSupport
