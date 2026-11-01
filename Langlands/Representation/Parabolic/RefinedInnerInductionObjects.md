# Smooth objects for induction inside refined blocks

`Langlands.CuspidalSupport.refinedInnerInductionObjects` takes a p-adic
field `F`, topological data `T`, an outer block shape `D`, a refinement `S`
and actual smooth tensor factors `C`. At each block it bundles
`RefinedInductionTensor.blockRepresentations F T D S C` as a smooth
representation, using `T.isSmooth_normalizedParabolicInduced`.

The carrier universe is `max uF uV`; the input factors have carrier universe
`uV`. The construction has no matching, admissibility or length hypothesis.

This definition was moved unchanged from
[AdjacentMatchingAssembly](../CuspidalSupport/AdjacentMatchingAssembly.md)
so that both its conditional cuspidal assembly and
[WholeLeviConjugacyProof](WholeLeviConjugacyProof.md) reuse the same object
without importing the conditional assembly into the whole-Levi proof.
Its existing namespace, parameters and construction are preserved.
