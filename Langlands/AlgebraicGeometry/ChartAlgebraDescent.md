# Effective finite étale algebra descent from chart transitions

This module supplies the algebra descent step of `finiteEtaleChartDescent` (`FiniteEtaleChartDescentProof`).

From a functorial chart-transition datum for `A → B → C`, with `B` faithfully
flat over `A` and `C` finite étale over `B`, this module constructs an actual
finite, projective, étale `A`-algebra and a `B`-algebra recovery isomorphism.
Every original chart transition fixes the recovered scalar extension of each
descended element. All rings stay in the original universe, including the
zero-ring cases. The chart map need not itself be étale.

The construction forms the actual coaction from the transition datum and
applies the existing faithfully flat invariant-algebra descent equivalence.
Finiteness, étaleness and projectivity are supplied by its existing descent
theorems. The universal chart-invariance lemma proves the final recovery law
for every original test algebra and pair of chart maps. Scalar structures
are normalized to the input ring maps for the coaction interface, and the
final constructor transports back to the original algebra structures.

This is an internal derivation. It introduces no additional effectivity,
cocycle or invariance premise beyond the given functorial chart laws and the
stated faithfully flat and finite étale hypotheses.
