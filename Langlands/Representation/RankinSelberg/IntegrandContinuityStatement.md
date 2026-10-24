# Continuity of the equal-rank quotient integrand

`Langlands.RankinSelberg.EqualRankIntegrandContinuousStatement F n` is an
internal proposition asserting continuity of the actual equal-rank JPSS
integrand on the left-unipotent quotient. The field has a topology with
continuous ring operations, and the real absolute value `abv` is assumed
continuous. The rank is `n+1`, including rank one.

For two smooth complex representations, an arbitrary unitary additive
character, standard and inverse-standard Whittaker functionals, vectors in
their actual coefficient images, a Schwartz–Bruhat row test and every
complex `s`, the conclusion is

```text
Continuous (equalRankIntegrand ψ abv f.val f'.val Φ s).
```

The representation universes are independent. No irreducibility,
admissibility, nonzero functional, finite-generation or convergence
hypothesis is imposed. No topology on either representation space is
required. The supplied field topology is retained throughout.

The provenance is internal: smooth matrix coefficients are locally
constant; the row map and determinant are continuous; the continuous
absolute value of an invertible determinant is strictly positive.
Complex power with fixed exponent is continuous on this positive real
locus. Multiplication gives continuity before descent, and the topology
of the actual left quotient transfers it to the representative-independent
integrand. In particular it is measurable for the Borel structure used in
the analytic statements. This module defines the continuity proposition;
it does not prove convergence or justify an integral interchange.
