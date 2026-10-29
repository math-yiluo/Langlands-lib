import Langlands.Algebra.LocalAlgebraApproximationExistenceProof
import Langlands.Algebra.LocalModuleApproximationReduction

/-! # Existence of local module approximation systems (Stacks 00QX) -/

universe uR uS uM

namespace Langlands.Algebra

/-- Stacks 00QX: an essentially finitely presented local algebra and a finitely presented module
admit one joint approximation system. -/
theorem localModuleApproximationExistence :
    LocalModuleApproximationExistenceStatement.{uR, uS, uM} :=
  localModuleApproximationExistence_of_localAlgebraApproximationExistence
    localAlgebraApproximationExistence.{uR, max uS uM}

example : LocalModuleApproximationExistenceStatement.{uR, uS, uM} :=
  localModuleApproximationExistence.{uR, uS, uM}

end Langlands.Algebra
