import Langlands.LocalFactor.CommonClosureGenerationProof
import Langlands.LocalFactor.Inductive.GallagherDeterminantProof
import Langlands.LocalFactor.NonabelianScalingReduction

/-!
# Additive-character scaling for actual exact virtual local constants

The published generation and Gallagher theorems discharge both premises of
the scaling reduction, proving the unchanged fixed-Haar scaling statement.
-/

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem

/-- Fixed-Haar additive-character scaling for every supplied actual
local-constant system, with independent field and representation universes. -/
theorem additiveCharacterScaling : AdditiveCharacterScalingStatement.{uF, uV} :=
  additiveCharacterScaling_of_generation_gallagher
    Langlands.LocalFactor.commonClosureDegreeZeroGeneration.{uF, uV}
    Inductive.gallagherDeterminant.{0, uF, max uF uV}

end Langlands.LocalFactor.NonabelianSystem
