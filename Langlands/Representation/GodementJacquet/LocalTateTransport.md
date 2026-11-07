# Scalar coordinates on the actual rank-one quotient

This internal construction extends the published scalar-to-GL1 Haar transport
from its p-adic realization to every nonarchimedean local field, including
positive characteristic. It imports the existing scalar group isomorphism,
rank-one quotient homeomorphism and their actual Haar measures unchanged.

`tateScalarQuotientHomeomorph` sends a unit `a` to the class of the scalar
one-by-one matrix with entry `a` in `N1 \ GL1`. It is the composition of the
existing continuous multiplicative scalar isomorphism with the inverse of the
existing rank-one quotient homeomorphism. It needs only a topological field.

For the measure assertions, the field has its valuative nonarchimedean local
structure, is Hausdorff, and the units and matrix group have Borel measurable
structures. The quotient assertions also require its Borel measurable
structure. There is no second countability or characteristic-zero premise.

The proof maps scalar multiplicative Haar to GL1. A homeomorphism transports
its regularity and Haar property. The preimage of the level-zero compact open
matrix subgroup is exactly the integral units, because the scalar entry and
its inverse are both integral precisely on this group. Both measures give
these groups mass one. Uniqueness of regular left Haar measures gives a
constant multiple, and evaluation on this compact open subgroup shows that
constant is one. This establishes exact measure preservation, transport of
integrability, and transport of all totalized complex integrals. Composing with
the quotient homeomorphism proves the corresponding quotient measure and
integral statements.

The provenance is internal: the proof uses the actual constructions in
`TateScalarTransport`, `RankOneQuotient`, and `RankinSelberg.Measures`, and
Mathlib's uniqueness of regular Haar measure. No local functional equation,
analytic continuation, normalized generator or conductor comparison is
asserted by this unit.
