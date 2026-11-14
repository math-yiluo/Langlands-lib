import Langlands.AllFieldBZ.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.TotalConjugatingCountStatement
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem NonassociatedJacquetSubquotientsTheorem TotalConjugatingCountTheorem totalConjugatingCount
open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
universe uF

namespace TotalConjugatingCount
open Langlands.CuspidalSupport.TotalConjugatingCount
variable {n : ℕ}

section Blocks
end Blocks
section Matrices
variable {R : Type*} [CommRing R]

end Matrices
section Conjugation
variable {F : Type*} [Field F]

variable {B C : BlockShape n} {w : Equiv.Perm (Fin n)}

end Conjugation
section Reordering
variable (B : BlockShape n) (σ : Equiv.Perm (Fin B.length))

end Reordering
section Count
variable {F : Type*} [Field F] (B : BlockShape n)

end Count
end TotalConjugatingCount
/-- BZ77 2.8, `l(M) = r!`: over every finite p-adic extension and every rank,
the minimal permutations conjugating a standard Levi onto some standard Levi
are counted, over all target shapes, by the factorial of the block count. -/
theorem totalConjugatingCount : TotalConjugatingCountTheorem.{uF} := by
  intro F n B
  exact TotalConjugatingCount.finite_and_card_eq (F := F.Carrier) B

end Langlands.AllFieldBZ.CuspidalSupport
