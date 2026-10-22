# Finite comparison and ordinary relative-to-absolute inflation

Author: Worker 42.

This construction imports the published generic comparison proof by Worker 54
through `Langlands.Cohomology.Continuous.CochainComparisonLawsProof`.
The local equivalence installs its explicit `continuousToOrdinary_isIso`
certificate, then packages that morphism as an additive equivalence. No
generic proof or statement is copied into this local contribution.

For a finite field extension `L/K`, the actual Krull topology on
`Gal(L/K)` is discrete. `continuousToRelativeEquiv K L n` therefore
packages the canonical forward comparison from `ClosureCoefficients`
as an additive equivalence using the generic proved
`Langlands.Continuous.continuousToOrdinary_isIso`. The forward map is
definitionally `continuousToRelative`, as its application certificate
records. The generic proof constructs an inverse on cochains by lifting
functions on finite tuples to nested continuous functions, proves the
inverse identities, and transports this isomorphism to actual cohomology.
No isomorphism or its existence is supplied as an additional hypothesis.

The base field and extension retain independent universes. Only their
finite dimensionality is needed for this equivalence; Galoisness is not
needed to compare continuous and ordinary cohomology of their actual
automorphism group. The coefficients remain the same discrete unit
representation over the lifted integers.

For a finite normal intermediate field `E` in the actual algebraic
closure of `K`, `closureInflation K E n` maps ordinary relative
cohomology to continuous absolute cohomology. It first uses the inverse
of `continuousToRelativeEquiv` and then the constructed continuous
inflation `closureContinuousInflation`. That inflation restricts actual
closure automorphisms to `E` and includes actual units into closure
units. Both the base field and this intermediate field lie in `Type u`;
no resizing is used.

`closureInflation_continuousToRelative` proves the commuting comparison
diagram by cancellation of the inverse equivalence. It does not assert
that inflation is injective. Such injectivity is a separate mathematical
claim, depending in degree two on Hilbert 90.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay
Greenberg, GTM 67, Springer, 1979. Source `serre-1979-local-fields`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.

Chapter X, section 3, printed page 154 (PDF page 160), describes
continuous Galois cohomology and its finite-stage inflation maps.
Chapter X, section 4, printed page 156 (PDF page 162), specifies the
compatible group and coefficient maps and the finite-to-absolute
passage. These passages were read in the retained original.

The local equivalence and cancellation certificates are derived
implementation work joining the two actual cochain models. They
specialize the generic cochain-comparison proof and the coefficient
maps, without changing either construction. No Frobenius sign choice
enters this comparison.
