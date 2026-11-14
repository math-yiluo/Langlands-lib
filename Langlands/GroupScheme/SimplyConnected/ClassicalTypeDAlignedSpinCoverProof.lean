import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDAlignedSpinCoverReduction
import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotient
import Langlands.GroupScheme.EvenOrthogonalForm.Proof

/-!
# Existence of type-`D` spin covers aligned with the numbered vector vertex

`classicalTypeDAlignedSpinCover` proves `ClassicalTypeDAlignedSpinCoverStatement` by applying
the reduction `classicalTypeDAlignedSpinCover_of_vectorQuotient` to the vector-quotient
theorem `typeDVectorQuotient` and Tits's realization `Quaternionic.evenSpecialOrthogonalForm`
of the forms of `SO_{2n}` as `O(q)⁰`.
-/

universe u

namespace Langlands.GroupScheme

/-- **Aligned type-`D` spin covers.** A simply connected, absolutely almost simple group of
type `D_n` (`n ≥ 4`) whose star action fixes the non-fork vertices has an aligned spin cover
`G ⟶ O(q)` for a nondegenerate quadratic form `q` over a central division algebra with an
orthogonal involution. -/
theorem classicalTypeDAlignedSpinCover : ClassicalTypeDAlignedSpinCoverStatement.{u} :=
  classicalTypeDAlignedSpinCover_of_vectorQuotient typeDVectorQuotient
    Quaternionic.evenSpecialOrthogonalForm

end Langlands.GroupScheme
