import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDSpinPresentationReduction
import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDAlignedSpinCoverProof
import Langlands.GroupScheme.SimplyConnected.AlignedSpinCoverTitsIndex

/-!
# Classical type-`D` spin presentations with index comparisons

`classicalTypeDSpinPresentation` proves `ClassicalTypeDSpinPresentationStatement` by applying
the reduction `classicalTypeDSpinPresentation_of_aligned` to two Library theorems:
`classicalTypeDAlignedSpinCover` (existence of a spin cover aligned with the vertex numbered
`0`) and `alignedSpinCoverTitsIndex` (the Witt index and the nonfork distinguished vertices
of any such cover).
-/

universe u

namespace Langlands.GroupScheme

/-- **Classical type-`D` spin presentation.** A simply connected, absolutely almost simple
group with a numbered Tits index of type `D_n` (`n ≥ 4`) whose star action fixes the nonfork
vertices has a spin cover `G ⟶ O(q)` for a nondegenerate quadratic form `q` over a central
division algebra with an orthogonal involution. The Witt index of `q` is the split rank of
`G`, and a nonfork vertex numbered `i` is distinguished exactly when `i + 1 = j * degree`
for some `0 < j` at most the Witt index. -/
theorem classicalTypeDSpinPresentation : ClassicalTypeDSpinPresentationStatement.{u} :=
  classicalTypeDSpinPresentation_of_aligned classicalTypeDAlignedSpinCover
    alignedSpinCoverTitsIndex

end Langlands.GroupScheme
