import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Modular characters of the actual rational-point group and its standard parabolics -/

universe u

namespace Langlands.Aubert.General.RationalPointFamily

/-- **Rational parabolic modulus.** For every connected reductive group over a
nonarchimedean local field, the actual rational-point group `G(k)` is unimodular, and
Mathlib's modular character of an actual standard parabolic `P = M ⋉ U` is the Haar
modulus of conjugation on its unipotent radical `U`. -/
theorem rationalParabolicModulus : RationalParabolicModulusStatement.{u} :=
  rationalParabolicModulus_of_reductiveUnimodularity rationalReductiveUnimodularity
    GroupScheme.dynamicCentralizerReductive

end Langlands.Aubert.General.RationalPointFamily
