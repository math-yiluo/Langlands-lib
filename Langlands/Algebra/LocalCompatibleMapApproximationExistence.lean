import Langlands.Algebra.LocalCompatibleMapApproximation
import Langlands.Algebra.LocalAlgebraApproximationExistenceProof

/-! # Simultaneous local approximation of a module map (Stacks 046Y, first proof step) -/

universe uR uS uM uN

namespace Langlands.Algebra

/-- The first paragraph of the proof of Stacks 046Y: Stacks 00QV for `R → ULift S`, combined
with the published reduction, gives one ring system with approximation systems of both modules
and compatible component maps inducing the given map. -/
theorem localCompatibleMapApproximationExistence :
    LocalCompatibleMapApproximationExistenceStatement.{uR, uS, uM, uN} :=
  localCompatibleMapApproximationExistence_of_localAlgebraApproximationExistence
    localAlgebraApproximationExistence.{uR, max uS uM uN}

end Langlands.Algebra
