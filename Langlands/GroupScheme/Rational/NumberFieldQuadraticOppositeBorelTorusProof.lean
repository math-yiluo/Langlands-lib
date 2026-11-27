import Langlands.GroupScheme.Rational.NumberFieldQuadraticOppositeBorelTorus
import Langlands.GroupScheme.Rational.QuadraticOppositeBorelExistence
import Langlands.GroupScheme.Rational.QuadraticOppositeBorelRealControl

/-! # Proof of the real-controlled reduction to a quadratic opposite-Borel torus -/

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- Platonov–Rapinchuk, Lemmas 6.17 and 6.28: a semisimple group over a number field that
is quasi-split over a totally imaginary quadratic Galois extension `Q` has a maximal torus
`T_Q = B ∩ σ(B)`, and every cocycle on `Spec Q → Spec F` trivial at the real places is
cohomologous to the image of a torus cocycle on the same cover, again trivial at the real
places. -/
theorem numberFieldQuadraticOppositeBorelTorus :
    NumberFieldQuadraticOppositeBorelTorusStatement.{u} := by
  intro F Q _ _ _ _ _ _ _ hQ G hG hqs
  obtain ⟨T, t, ht⟩ := exists_quadraticOppositeBorelTorus hQ hG.isConnectedReductive hqs
  exact ⟨T, t, ht, fun ξ hξ =>
    ht.exists_realLocallyTrivialRepresentative hG.isConnectedReductive ξ hξ⟩

end Langlands.GroupScheme
