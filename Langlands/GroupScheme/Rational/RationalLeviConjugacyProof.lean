import Langlands.GroupScheme.Rational.DynamicLeviConjugacyReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Dynamic.UnipotentCocharacterConjugacy

/-! # Rational conjugacy of Levis of a parabolic: proof -/

universe u

namespace Langlands.GroupScheme

/-- **Rational Levi conjugacy** (Borel–Tits 1965, Corollary 3.14, for parabolics). Two
supplied rational Levis of a rational parabolic of a connected reductive group are conjugate
by a unique rational point of any specified geometric unipotent radical. -/
theorem rationalLeviConjugacy : RationalLeviConjugacyStatement.{u} :=
  DynamicLeviConjugacy.rationalLeviConjugacy_of_dynamic parabolicDynamic
    dynamicGeometricUnipotentRadical
    (fun _ _ _ _ χ ψ h => Dynamic.exists_unipotent_conj_of_mul_inv_mem χ ψ h)

end Langlands.GroupScheme
