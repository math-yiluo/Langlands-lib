# Coherent actual orbit comparison squares

This internal specialization fixes one family of actual compatible orbital
measures for each target shape and permutation and uses it at every
source-increasing shape. The family is independent of the coefficient
representation.

`coherentCutOrbitIntegralValue` evaluates the actual supplied-measure compact
orbit equivalence on genuine target-radical coinvariants using
`parabolicOrbitCoherentMeasures`. The coefficient representation is the
normalized Jacquet module with the existing positive source half modulus and
the actual integrated Haar-ratio coefficient.

`coherentCutOrbitIntegralValue_cutMap` gives the actual coefficient square
for every inclusion of source cuts on which the permutation is source
increasing at both ends. Its pointwise hypothesis says precisely that the
target compact representative is the genuine Jacquet quotient projection
of the source representative. The proof specializes the supplied-measure
comparison and rewrites its transported measure datum by literal coherence
of the family. Consequently all these squares use the same measures at
every admissible shape; there is no further normalization choice.

`correctedOrbitRestriction_coherent_comparison_cutMap` gives the square for
the actual corrected-support restriction after the canonical support quotient
projection. The implemented support-preserving cut map supplies the
pointwise hypothesis. The support and lower-support sets retain their upward
closure assumptions, and the permutation belongs to the corrected two-sided
Weyl support.

These are equalities of actual orbit-equivalence values. Arbitrary primes,
supplied fields and topologies, ranks including zero, and independent field
and coefficient universes are retained. This module does not identify an
entire graded complex or prove a homology or effectivity statement.
