# Actual root rays from the apartment axioms

This internal construction derives real coroot vectors and actual root-ray
disjointness from the unchanged `SatisfiesApartmentAxioms` assumptions. It
uses no general relative-root-system or rank-one factorization theorem.

For each actual relative root, the derivative-root equality supplies an actual
affine root with that derivative. Its affine coroot has self-pairing two and
integral cross-pairings with every other affine root. Lifting that vector
from the apartment translation quotient to the real cocharacter space gives
`integralRootCoroot`. Integrality refers to its pairings with the actual roots;
the vector is not asserted to be an integral cocharacter.

If `m*a=n*b` for positive natural numbers `m,n`, evaluating at the two chosen
vectors gives positive integral cross-pairings whose product is four. Their
possible pairs are `(1,4)`, `(2,2)` and `(4,1)`. These force `a=2*b`, `a=b`,
or `b=2*a`, using injectivity of characters in their rational scalar extension
for the split torus. Distinct actual indivisible roots therefore have disjoint
positive integral rays. The argument is vacuous if there are no roots.

The provenance is internal derived mathematics from the published apartment
axioms, affine coroot axioms, root forms and split-torus character injection.
No new assertion from original literature is introduced. This is a local
consequence for the supplied actual apartment, not the arbitrary-field global
relative-root-ray decomposition proposition.
