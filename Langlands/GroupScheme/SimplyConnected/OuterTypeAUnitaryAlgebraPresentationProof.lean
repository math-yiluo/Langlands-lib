import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitaryAlgebraReduction
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleProof

/-! # Outer forms of type A are special unitary groups of algebras with involution

Proof of `OuterTypeAUnitaryAlgebraPresentationStatement`, by applying the conditional
reduction `OuterTypeAUnitaryAlgebra.outerTypeAUnitaryAlgebraPresentation_of_specialLinearTitsCocycle`
to the proved `specialLinearTitsCocycle`.
-/

universe u

namespace Langlands.GroupScheme

/-- **Outer forms of type A.** Every simply connected absolutely almost-simple group of outer
type `A_n` over a field is the special unitary group `SU(B, τ)` of a central simple algebra of
degree `n + 1` over a separable quadratic extension, with an involution of the second kind. -/
theorem outerTypeAUnitaryAlgebraPresentation :
    OuterTypeAUnitaryAlgebraPresentationStatement.{u} :=
  OuterTypeAUnitaryAlgebra.outerTypeAUnitaryAlgebraPresentation_of_specialLinearTitsCocycle
    specialLinearTitsCocycle

end Langlands.GroupScheme
