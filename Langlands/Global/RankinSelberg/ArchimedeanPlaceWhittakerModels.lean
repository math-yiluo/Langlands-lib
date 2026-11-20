import Langlands.Global.RankinSelberg.RealUniformLocalTheoryReduction
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof

/-! # Actual Whittaker model comparison at real and complex places -/

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- The model comparisons for actual place restrictions hold at both kinds of
infinite places, for both additive characters. -/
def ArchimedeanPlaceWhittakerModelsStatement : Prop :=
  RealPlaceUniformWhittakerModelStatement.{u} ∧ ComplexPlaceWhittakerModelStatement.{u}

/-- Combine the real uniform model comparison with the complex analytic bridge. -/
theorem archimedeanPlaceWhittakerModels : ArchimedeanPlaceWhittakerModelsStatement.{u} :=
  ⟨realPlaceUniformWhittakerModel, complexPlaceWhittakerModelReduction
    (complexPlaceWhittakerIntertwinerReduction complexPlaceWhittakerAnalytic)⟩

end Langlands.Global.RankinSelbergGlobal
