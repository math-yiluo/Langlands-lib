# Continuous cohomology of separable-closure units

For an integral field extension `S/K`, `galoisUnitModule` uses the Krull
topological group of K-automorphisms of S and the units of S with the
discrete topology. The coefficient notation is additive and the scalar
ring is the universe lift of the integers. The action is the Galois action
on the units, and its joint continuity follows from the open unit
stabilizers. `separableH2` specializes Mathlib's continuous cohomology to
degree two for `S = SeparableClosure K`.

Restriction to an embedded normal subextension is continuous. The image of
a finite intermediate field under the embedding remains finite. Its fixing
subgroup in the larger Krull group maps into the fixing subgroup of the
original intermediate field, giving continuity at the identity and hence
everywhere.

For any finite normal stage `L/K` with an inclusion into `S` over `K`,
`relativeToContinuous` first uses the inverse of the existing comparison
from continuous to ordinary cohomology for the discrete Krull topology
of `Gal(L/K)`. It then applies the cohomology map given by restriction of
S-automorphisms and inclusion of L-units. In a tower of finite normal
stages, the group maps compose by restriction and the coefficient maps
compose by field inclusion. Functoriality on cochains and the finite-group
comparison give `relativeToContinuous_tower` in every degree.

This implements the passage to separable-closure coefficients in
J.-P. Serre, *Local Fields* (1979), Chapter X, §5, printed p. 159, using
Mathlib's continuous-cochain complex. The definitions and tower calculation
apply to fields of arbitrary characteristic, including imperfect fields.
