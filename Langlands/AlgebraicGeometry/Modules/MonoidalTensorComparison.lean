import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import Langlands.AlgebraicGeometry.Modules.Tensor

/-! # The monoidal and explicit sheafified tensor products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- The monoidal tensor product agrees with the explicit sheafified tensor product. -/
def monoidalTensorIso (A B : X.Modules) :
    Scheme.Modules.tensor A B ≅ Langlands.Scheme.Modules.tensorObj A B :=
  (Scheme.Modules.tensorIsoSheafify A B).symm

end Langlands.AlgebraicGeometry.Modules
