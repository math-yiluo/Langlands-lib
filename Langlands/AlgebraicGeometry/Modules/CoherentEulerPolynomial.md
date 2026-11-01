# Coherent Euler polynomials from support induction

This internal module derives polynomiality from the actual coherent Euler sequence
on a noetherian separated scheme proper over a field. A coherent module here means
a quasi-coherent module with finite sections on every affine open. A closed support
bound `HasSupportDimensionLT M e` forces the `e`th iterated step-one difference of
its Euler sequence to vanish.

The proof inducts on `e` and, for a fixed positive `e`, on the closed support
witness. An empty witness forces the module to be zero. Otherwise the published
noetherian topology lemma chooses an irreducible closed subset `T` and an open
whose intersection with the support lies in `T`. An affine refinement also
trivializes the given line bundle. The map from `M` to the pushforward of its
restriction to that affine open has coherent image `I`. Its kernel is supported
on a proper closed subset of the original witness, so closed-set induction
applies to it.

The image `I` and its line-bundle twist vanish off `T` and are isomorphic on the
chosen affine open. The coherent graph comparison expresses their difference
through four errors whose support bounds have decreased by one. The outer
induction kills the corresponding differences. Twisting shifts the Euler sequence,
so this proves the required next difference for `I`. Actual Euler additivity for
the short exact sequence from the kernel through `M` onto `I` finishes the step.

`coherentEulerPolynomial` is the rational Newton polynomial of this actual sequence.
The published finite-difference reconstruction proves that it agrees at every
natural argument, including zero, whenever the support dimension is at most `d`;
its natural degree is at most `d`. The final comparison theorem removes the
induction hypothesis from the earlier graph comparison: an affine identification
meeting irreducible support of height at most `d` makes the `d`th difference of the
two Euler sequences equal.

The provenance is internal: the module combines the published noetherian
closed-set argument, coherent closure and graph support results, actual Euler
identities, and rational Newton reconstruction. It assumes no polynomiality or
positivity certificate. It does not prove the positive leading term for ample
line bundles.
