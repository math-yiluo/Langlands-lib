import Langlands.GroupScheme.Rational.NumberFieldQuadraticOppositeMinimalParabolicLevi
import Langlands.GroupScheme.Rational.QuadraticOppositeMinimalParabolicExistence
import Langlands.GroupScheme.Rational.QuadraticOppositeMinimalParabolicRealControl

/-! # Proof of the real-controlled reduction to a quadratic opposite minimal parabolic Levi -/

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- Platonov–Rapinchuk, Lemmas 6.17' and 6.28', for the minimal parabolic subgroups: a
semisimple group over a number field has, for a totally imaginary quadratic Galois extension
`Q`, a closed subgroup `C` with `C_Q = P ∩ σ(P)` a Levi subgroup of a minimal parabolic subgroup
`P` of `G_Q`, and every cocycle on `Spec Q → Spec F` trivial at the real places is cohomologous
to the image of a cocycle of `C` on the same cover, again trivial at the real places. -/
theorem numberFieldQuadraticOppositeMinimalParabolicLevi :
    NumberFieldQuadraticOppositeMinimalParabolicLeviStatement.{u} := by
  intro F Q _ _ _ _ _ _ _ hQ G hG
  let : Infinite F := inferInstance
  obtain ⟨C, t, ht⟩ := exists_quadraticOppositeMinimalParabolicLevi hQ hG.isConnectedReductive
  exact ⟨C, t, ht, fun ξ hξ =>
    ht.exists_realLocallyTrivialRepresentative hG.isConnectedReductive ξ hξ⟩

end Langlands.GroupScheme
