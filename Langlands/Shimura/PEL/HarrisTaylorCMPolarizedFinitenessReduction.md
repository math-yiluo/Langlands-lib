# CM rigidity from polarized-automorphism finiteness

Author: Worker 335.

`CMRigidityFromPolarizedAutomorphismFinitenessStatement` is an internal
conditional reduction. With the exact datum, signature charts, universe and
named prerequisites of the original `CMSmallLevelRigidityStatement`, it says
that `PolarizedAutomorphismFinitenessStatement` implies that unchanged target.
The geometric finiteness proposition remains a premise.

`cmRigidityFromPolarizedAutomorphismFiniteness` proves this implication by
applying the published `cmRigidityFromIntegralPolarizedAutomorphisms` reduction.
For its integral finite-order premise, the supplied geometric theorem makes the
actual subgroup of automorphisms preserving the actual polarization finite.
The original automorphism, together with its integral preservation equation,
defines an element of this subgroup. The finite-group theorem gives finite
order there. Mapping its positive power equation through the subgroup inclusion
gives finite order in `Aut B` with the same exponent.
The subgroup's constructed dual and polarization predicate are exactly those
specified by the original dual witness.

For the second premise, the published
`Langlands.AbelianScheme.Tate.fieldPrimeRationalFaithfulness` is specialized
to the actual scheme `B` as both source and target, at the same prime.
It supplies injectivity of the existing actual rational prime Tate Hom map
at the identity field point. No faithfulness premise remains in this reduction.

The provenance is the internal composition of these published constructions
and the elementary subgroup finite-order transfer. No geometric finiteness
proof is claimed here. The remaining proposition is the exact target of
Task 6765; the original rigidity statement and its import closure are unchanged.
