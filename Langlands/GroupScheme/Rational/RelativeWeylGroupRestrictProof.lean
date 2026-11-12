import Langlands.GroupScheme.Rational.RelativeWeylRestrictReduction
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.MinimalParabolicSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicNormalizerProof

/-! # The relative Weyl group is the same over every connected test scheme

The published reduction to five structural statements is instantiated with published proofs
of all five. -/

universe u

namespace Langlands.GroupScheme

/-- **Borel–Tits 5.3; Milne 25.16(b)(c) and 25.17.** For a maximal split torus `i` of a
connected reductive group over a field `k` and every connected `k`-scheme `U`, restriction
`N(k)/Z(k) → N(U)/Z(U)` is bijective. -/
theorem relativeWeylGroupRestrict_bijective : RelativeWeylGroupRestrictStatement.{u} :=
  relativeWeylGroupRestrictStatement_of_structuralInputs
    ⟨genericMinimalParabolic, minimalParabolicConjugacy, minimalParabolicSplitTorusConjugacy,
      genericCentralizer, parabolicSelfNormalizer⟩

end Langlands.GroupScheme
