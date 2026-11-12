import Langlands.GroupScheme.Reductive.LocalWeylNormalizationProof
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationField

/-! # Weyl normalization over reduced local rings -/

universe u

namespace Langlands.GroupScheme.LocalSplitCell

/-- The exact published proposition, with its structural inputs discharged. -/
theorem localWeylNormalization :
    LocalWeylNormalizationStatement.{u} :=
  localWeylNormalization_of_field fieldWeylNormalization

end Langlands.GroupScheme.LocalSplitCell
