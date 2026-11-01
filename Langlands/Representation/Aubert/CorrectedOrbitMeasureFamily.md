# A coherent family of actual orbit measures

This internal construction supplies all source shapes at once for a fixed
actual target and permutation. It retains every field of the supplied actual
compatible measure data.

The kernel cut equivalences compose because each retains the same actual
radical element. Restriction gives the intersection composition theorem, and
quotient induction gives the quotient composition theorem. Two supplied
measure data are equal when their kernel, intersection and quotient measures
are equal; the remaining fields are proofs. Applying pushforward composition
to these three measures proves `parabolicOrbitIntegralMeasures_cutMap_comp`.

`parabolicOrbitIncreasingBase` is the shape whose cuts are exactly the
permutation descents. The existing block-increasing characterization proves
that this shape is source increasing and that its cuts are contained in those
of every other source-increasing shape.

`parabolicOrbitCoherentMeasures` chooses the actual compatible measure data
once at this base and transports all three measures to each source-increasing
shape. The construction is independent of coefficient representations.
`parabolicOrbitCoherentMeasures_cutMap` proves literal equality between the
family at the target source shape and the simultaneous pushforward of the
family at the original source shape. Thus the family works for every
inclusion of admissible source cuts at once, without scalar renormalization.
The construction retains arbitrary primes, supplied fields and topologies,
and ranks including zero. No homology or effectivity assertion is made.
