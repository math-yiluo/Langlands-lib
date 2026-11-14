import Langlands.Representation.Whittaker.InducedLocalizationProof
import Langlands.AllField.Representation.Whittaker.InducedLocalizationAssembly
/-! # Character-localized heredity for upper block induction

The four closed prerequisite theorems discharge every input of the published
geometric assembly, proving the unchanged full quotient statement.
-/

namespace Langlands.AllField

universe uF uV

/-- The character quotient of upper unnormalized block induction is linearly
equivalent to the tensor of the block character quotients. -/
theorem inducedLocalization : InducedLocalizationStatement.{uF, uV} :=
  Langlands.AllField.Whittaker.inducedLocalization_of_prerequisites
    Langlands.AllField.Whittaker.unipotentOrbit.{uF}
    Whittaker.nonOpenCharacterWitness.{uF}
    Langlands.AllField.Whittaker.compactLocalization.{uF, uV}
    Jacquet.Localization.filtrationCollapse.{uF, max uF uV}

end Langlands.AllField
