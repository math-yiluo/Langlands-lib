# Parabolic double-coset assembly through the supplied Levi bridge

Authors: Worker 1336 and Worker 1340.

This internal derived module connects the supplied-torus-to-supplied-Levi
construction to the double-coset representative reduction. It provides a
chosen representative and a conditional final assembly. The six structural
propositions in the final assembly remain premises; this module does not
prove the closed `RepresentedParabolicDoubleCosetStatement`.

The theorem
`parabolicSplitTorusLeviConjugacyStatement_of_dynamic_and_smoothConjugacy`
proves the moving-torus interface from `ParabolicDynamicStatement` and
`SmoothMaximalSplitTorusConjugacyStatement`. An actual factorization
`f ≫ p = i` implies
`SubgroupFunctor.range i ≤ SubgroupFunctor.range p` by
`SubgroupFunctor.range_le_of_factor`. The theorem
`ParabolicLeviTorus.exists_point_and_factor` then supplies the rational
point of the given parabolic and the factor through the given Levi,
with the same original torus source. All-test containment, rationality
and the direction of inner conjugation are preserved.

The definition `torusAdaptedParabolicRepresentative` additionally assumes
`ParabolicIntersectionCentralizerStatement`. The existing theorem
`parabolicIntersectionSplitTorusStatement_of_centralizer` supplies a common
ambient maximal split torus with actual factors through the two parabolics.
The representative theorem applies this common-torus statement and the
new moving-torus adapter to the supplied parabolics, Levis and rational
point `g`. Classical choice selects a rational point `z` in the same literal
double coset. Its subtype certificate asserts an ambient maximal split
torus and both group-scheme factorization equations, through `M` and
through `z L z⁻¹`. No finiteness assertion is needed to choose this point.

Finally,
`representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs`
combines this adapter and the centralizer-to-common-torus reduction with
`representedParabolicDoubleCosetStatement_of_structural_inputs`. Its six
premises are exactly `RationalBruhatStatement`,
`GenericMinimalParabolicStatement`, `MinimalParabolicConjugacyStatement`,
`ParabolicIntersectionCentralizerStatement`, `ParabolicDynamicStatement`
and `SmoothMaximalSplitTorusConjugacyStatement`, at universe `u`.
Finiteness uses the first three premises; the torus representative uses
the last three. None is proved by this composition, and none may remain
a hypothesis in the host task's final closed proof.

The provenance is the composition of the named Library constructions and
reductions, rather than a separate translation of a literature assertion.
The underlying representative calculation and Levi bridge are explained
in the paired `ParabolicDoubleCosetRepresentatives` and
`ParabolicLeviTorusConjugation` modules. This module adds the explicit
factor-to-range adapter, the chosen representative and the combined
dependency interface. It introduces no additional field restrictions.
