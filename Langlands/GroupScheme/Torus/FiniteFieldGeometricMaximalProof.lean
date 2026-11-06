import Langlands.GroupScheme.Torus.FiniteFieldGeometricAssembly
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof

/-! # Geometrically maximal tori over finite fields -/

universe u

namespace Langlands.GroupScheme

/-- Every smooth connected affine group over a finite field has an actual torus
inclusion maximal both over that field and after extension to its algebraic closure. -/
theorem finiteFieldGeometricMaximalTorus : FiniteFieldGeometricMaximalTorusStatement.{u} :=
  finiteFieldGeometricMaximalTorus_of_maximalTorusConjugacy maximalTorusConjugacy

end Langlands.GroupScheme
