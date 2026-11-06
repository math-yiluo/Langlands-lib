# Combining reciprocity comparison with fixed-system epsilon inheritance

This module gives an internal logical reduction using the published
`AssemblyPairEpsilonSystemInheritance` interface and the published geometric
Weil reciprocity uniqueness proposition. It introduces no external literature
assertion. Both imported propositions retain their existing definitions.

`AssemblyEpsilonInheritanceReductionStatement.{uF, uP, uA} F` is the implication
from `GeometricWeilReciprocityUniqueness.{uF}` and
`AssemblyPairEpsilonSystemInheritance.{uF, uP, uA} F` to the unchanged
`AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F`. The parameter and
automorphic carrier universes remain independent.

The theorem
`assemblyEpsilonInheritance_of_geometricUniqueness_and_systemInheritance`
proves this conditional statement. It assumes the full-universe geometric
Weil reciprocity uniqueness proposition and fixed-system epsilon inheritance
over `F`. Neither premise is proved in this module.

The implemented proof opens the existential part of
`IsSupercuspidalCorrespondence F c0`. This supplies a geometric candidate
`e0`, a reciprocity family `eC`, an assignment `ε`, a system proof `hε`,
the identity `IsBaseReciprocity F e0 eC`, and the supercuspidal pair-factor
compatibility for that system. Geometric uniqueness at
`F.canonicalTopologicalData` gives `e = e0`. Substituting this equality
establishes `IsBaseReciprocity F e eC`. The fixed-system inheritance premise
then gives full pair epsilon compatibility for `c` with the same
`eC`, `ε`, and `hε`.

In particular, the system is selected before any additive character is
introduced. Its measure requirements are those of the full pair
compatibility supplied by the premise; the combination makes no extra
local-constant or measure existence assumption.

The host target keeps its original hypotheses and is not changed by this
helper. An unconditional proof of the host task still requires proofs of
both premises. In particular, this module does not prove reciprocity
uniqueness, segment-level epsilon inheritance, or the classification inputs
of fixed-system inheritance.
