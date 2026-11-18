import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralizerOpenReduction
import Langlands.GroupScheme.Torus.DiagonalizableCentralizerOpen

/-! # Proof: the centralizer of a subgroup of multiplicative type is open in its normalizer -/

universe u

namespace Langlands.GroupScheme

/-- **The centralizer of a subgroup of multiplicative type is open in its normalizer**
(Milne, *Algebraic Groups* (2017), Corollary 12.40). The published reduction to the split
diagonalizable case is fed the published split diagonalizable theorem. -/
theorem multiplicativeTypeCentralizerOpen : MultiplicativeTypeCentralizerOpenStatement.{u} :=
  multiplicativeTypeCentralizerOpen_of_diagonalizable
    (fun k _ M _ _ G N C i hi n c hn hc =>
      diagonalizableCentralizer_isOpenImmersion_field k M G N C i hi n c hn hc)

end Langlands.GroupScheme
