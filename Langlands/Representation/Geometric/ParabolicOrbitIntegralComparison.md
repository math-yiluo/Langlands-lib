# Orbit comparison with supplied compatible measures

This internal construction exposes the actual relative-integral comparison
with its measure choices as explicit data. `ParabolicOrbitIntegralMeasures`
contains regular two-sided Haar measures on the actual nested kernel and its
actual stabilizer intersection, a quotient measure finite on compact sets, and
the actual compatibility property, including the Weil integral formula.
The measurable spaces are the canonical Borel structures.

For the supplied p-adic topology, `parabolicOrbitIntegralMeasures_nonempty`
packages the proved nested-kernel measure existence theorem. This existence
does not depend on a coefficient representation.

`parabolicOrbitCompactIntegralEquiv` takes these supplied data and a smooth
complex representation of the source Levi. It composes the existing compact
stages relative-integral equivalence with the identity-on-vectors comparison
between the generic split-kernel Haar character and the actual parabolic
Haar-ratio character. Its source is actual unnormalized target-Levi
coinvariants of the compact orbit representation; its target is actual compact
induction from the stages quotient with the existing integrated coefficient.
The positive inducing half modulus remains the existing one.

`parabolicOrbitIntegralKernelSlice` is the actual compact stages slice.
`parabolicOrbitIntegralIntegrand` descends it to the actual quotient; its
`_mk` theorem evaluates to the coefficient coinvariant class of the original
orbit function at the kernel element times the Levi section.

`parabolicOrbitCompactIntegralEquiv_eval_mk` proves that every representative
evaluates by integrating the genuine compact stages kernel slice against the
supplied quotient measure. It applies the implemented generic integral
evaluation theorem; the coefficient comparison and postcomposition preserve
the actual values, so no scalar normalization is hidden.

The results retain arbitrary primes, supplied fields and topologies, independent
field and coefficient universes, and every natural rank including zero. They
do not yet select compatible measure families across source cuts or prove
cross-cut equivalence squares, lower homology vanishing or signed effectivity.
