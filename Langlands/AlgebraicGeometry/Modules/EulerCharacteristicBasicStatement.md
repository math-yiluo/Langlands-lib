# Basic identities for actual cohomological Euler characteristics

`DerivedSections.EulerCharacteristicBasicStatement` groups five elementary
properties of the actual Euler invariant over an arbitrary field:

- A cohomological vanishing bound computes the invariant by the ordinary
  alternating sum over degrees below that bound.
- An actual isomorphism of module sheaves preserves finite cohomology.
- Such an isomorphism preserves the integer Euler characteristic.
- A sheaf with zero cohomology in every nonnegative degree has invariant zero.
- If all positive cohomology vanishes, the invariant is the dimension of the
  actual zeroth cohomology vector space.

Every Euler value retains its explicit finite-cohomology proof argument. All
cohomology and scalar actions are those of `relativeCohomology f n`; the
isomorphism is in the actual category `X.Modules`. No abstract replacement
cohomology family, properness or coherence assumption is introduced.

This is an internal derived statement. Its provenance is the published
`EulerCharacteristic` definition, functorial transport of categorical zero
objects and finite-dimensional vector spaces, Mathlib's isomorphism invariance
of `Module.finrank`, and the finite-support interpretation of `finsum`. A zero
cohomology object has zero vector-space dimension, so the chosen vanishing bound
contains the support of the alternating summand. The last two assertions are
its specializations at bounds zero and one. This file states these properties;
it does not prove them or assert short-exact-sequence additivity, polynomiality
or a numerical rank formula.
