import Langlands.Algebra.LocalAlgebraApproximationTransition

/-! # Existence of local algebra approximation systems (Stacks 00QV) -/

universe uR uS

namespace Langlands.Algebra

open LocalAlgebraApproximationExistence in
/-- Stacks 00QV: every essentially finitely presented local algebra map admits a directed local
algebra approximation system. -/
theorem localAlgebraApproximationExistence :
    LocalAlgebraApproximationExistenceStatement.{uR, uS} :=
  fun R S _ _ _ _ _ _ hS ↦ exists_isApproximation R S hS fun P _ _ h ↦
    P.isPrimeLocalization_system h

example : LocalAlgebraApproximationExistenceStatement.{uR, uS} :=
  localAlgebraApproximationExistence.{uR, uS}

end Langlands.Algebra
