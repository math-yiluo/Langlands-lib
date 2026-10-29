import Langlands.Representation.Whittaker.InducedLocalizationAssembly
import Langlands.Representation.Whittaker.UnipotentOrbitProof
import Langlands.Representation.Whittaker.NonOpenCharacterProof
import Langlands.Representation.Whittaker.CompactLocalizationProof
import Langlands.Representation.Jacquet.LocalizationFiltrationCollapseProof

/-! # Character-localized heredity for upper block induction

The four closed prerequisite theorems discharge every input of the published
geometric assembly, proving the unchanged full quotient statement.
-/

namespace Langlands

universe uF uV

/-- The character quotient of upper unnormalized block induction is linearly
equivalent to the tensor of the block character quotients. -/
theorem inducedLocalization : InducedLocalizationStatement.{uF, uV} :=
  Whittaker.inducedLocalization_of_prerequisites
    Whittaker.unipotentOrbit.{uF}
    Whittaker.nonOpenCharacterWitness.{uF}
    Whittaker.compactLocalization.{uF, uV}
    Jacquet.Localization.filtrationCollapse.{uF, max uF uV}

end Langlands
