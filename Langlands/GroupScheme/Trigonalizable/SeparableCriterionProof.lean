import Langlands.GroupScheme.Trigonalizable.CharacterizationProof
import Langlands.GroupScheme.Trigonalizable.SeparableCriterionReduction

/-! # Proof of Milne 16.6: becoming trigonalizable over a separable extension -/

universe u

namespace Langlands.GroupScheme

/-- Milne, Theorem 16.6. An affine algebraic group `G` over `k` becomes trigonalizable over a
separable extension of `k` iff it has a normal unipotent closed subgroup `U` with an fppf quotient
onto a group of multiplicative type. When this holds, `U` contains every unipotent closed
subgroup of `G`. -/
theorem separablyTrigonalizableCriterion : SeparablyTrigonalizableCriterionStatement.{u} :=
  SeparableTrigonalization.separablyTrigonalizableCriterion_of_characterization
    trigonalizableCharacterization

end Langlands.GroupScheme
