import Langlands.Automorphic.GroupSchemeLeviCenterRestrictionReduction
import Langlands.Algebra.ParabolicCenterProjectionFiniteProof
import Langlands.Automorphic.GroupSchemeParabolicTangentProof

/-! # Finite Levi restriction of the actual archimedean enveloping centres

For a rational parabolic subgroup of a connected reductive group over a number field, with a
rational Levi subgroup and its unipotent radical, the actual archimedean enveloping centre of the
group restricts along the Levi point map, on functions invariant under the unipotent radical
points, through a finite algebra map to the actual archimedean enveloping centre of the Levi
(Mœglin–Waldspurger I.2.17; Harish-Chandra 1968, Chapter I, §6).

The theorem combines the reduction `parabolicLeviCenterRestrictionReduction` with its two
inputs: the finiteness of Harish-Chandra's parabolic projection for reductive complex Lie algebras
(`Langlands.Algebra.ParabolicCenterProjection.parabolicCenterProjectionFinite`) and the
archimedean tangent grading of a rational parabolic (`parabolicLeviTangentGrading`).
-/

universe u

namespace Langlands.Automorphic.GroupSchemeFunctions

/-- Finite Levi restriction of the actual archimedean enveloping centres
(Mœglin–Waldspurger I.2.17). -/
theorem parabolicLeviCenterRestriction : ParabolicLeviCenterRestrictionStatement.{u} :=
  parabolicLeviCenterRestrictionReduction
    Langlands.Algebra.ParabolicCenterProjection.parabolicCenterProjectionFinite
    parabolicLeviTangentGrading

end Langlands.Automorphic.GroupSchemeFunctions
