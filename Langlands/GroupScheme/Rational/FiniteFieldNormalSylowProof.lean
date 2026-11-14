import Langlands.GroupScheme.Rational.FiniteFieldBorelSylow

/-! # The finite-field normal Sylow torus criterion -/

universe u

namespace Langlands.GroupScheme

/-- The published normal Sylow torus criterion, at arbitrary universe. -/
theorem finiteFieldNormalSylowTorusProof :
    FiniteFieldNormalSylowTorusStatement.{u} :=
  finiteFieldNormalSylowTorus.{u}

end Langlands.GroupScheme
