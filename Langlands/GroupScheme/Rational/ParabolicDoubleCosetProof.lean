import Langlands.GroupScheme.Rational.ParabolicDoubleCosetAssembly
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicIntersectionCentralizerProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof

/-! # Finite parabolic double cosets with torus-adapted representatives: proof -/

universe u

namespace Langlands.GroupScheme

/-- **Borel–Tits 5.20, Renard V.4.5–V.4.7.** For actual parabolic subgroups with rational
Levi subgroups of a connected reductive group over any field, the double cosets of the
literal rational point images are finite, and every double coset has a representative `z`
such that some maximal split torus lies in `M` and in `z L z⁻¹`. -/
theorem representedParabolicDoubleCoset : RepresentedParabolicDoubleCosetStatement.{u} :=
  representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs
    rationalBruhat genericMinimalParabolic minimalParabolicConjugacy
    parabolicIntersectionCentralizer parabolicDynamic smoothMaximalSplitTorusConjugacy

end Langlands.GroupScheme
