import Langlands.GroupScheme.Unipotent.MultiplicativeExtensionPartReduction
import Langlands.GroupScheme.Trigonalizable.ExtensionSplitAlgClosed

/-! # The unipotent part of an extension of a multiplicative group (Milne 16.8, 16.10) -/

universe u

namespace Langlands.GroupScheme

/-- Milne 2017, Notes 16.8 and 16.10: the unipotent part `G_u` of an affine algebraic group
satisfying the conditions of Theorem 16.6 is the smallest normal subgroup with a quotient of
multiplicative type, its formation commutes with field extension, and it is smooth (resp.
connected) when `G` is. -/
theorem multiplicativeExtensionUnipotentPart :
    MultiplicativeExtensionUnipotentPartStatement.{u} :=
  multiplicativeExtensionUnipotentPart_of_algClosedSplitting
    fun _ _ _ _ _ _ _ i _ _ _ q hi hU hn hq =>
      TrigonalizableExtensionSplit.exists_section_of_isAlgClosed i q hi hU hn hq

end Langlands.GroupScheme
