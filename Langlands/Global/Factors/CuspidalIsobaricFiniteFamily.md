# Construction of the finite-place family of cuspidal isobaric sums

`Langlands.Global.cuspidalIsobaricFiniteFamily` proves
`Langlands.Global.CuspidalIsobaricFiniteFamilyStatement`.

## Proof

At each finite place `v`, take the canonical p-adic objects of the supplied
local components. Their irreducibility lets `exists_isIsobaricSum` construct
a smooth isobaric sum at rank `r + 1`. Its head condition implies
irreducibility by `IsIsobaricSum.isIrreducible`. Apply
`TwoFactorCommutativity.isAdmissible_of_isIrreducible` to package the sum as an
`AutomorphicObject`. Choose these objects as a single family indexed by the
finite places.

At each place apply `IsIsobaricSum.isSubquotient_normalizedProduct` to the
block shape given by `m` and `hm`. Its normalized product for the canonical
topological data is the required canonical induction.

Take `S` to be the finite union of the presentations' exceptional sets.
For `v ∉ S`, `hasSphericalSpectrum_padicObject` supplies a spherical
constituent witness for each input. Its fixed-vector clause gives a nonzero
integral fixed space. The local theorem `isSpherical_of_isIsobaricSum` gives
the same property for the sum `A v`.

## Provenance

The construction implements the local part of Getz–Hahn (2024), proof of
Theorem 10.7.5, p. 288 (PDF p. 300). It uses multisegment pooling for (10.33),
p. 284 (PDF p. 296), the finite iteration of Tadić (1986), Proposition A.4(ii),
p. 372 (PDF p. 39), for the subquotient step, and spherical constituents of
ordered unramified principal series for the sphericity step of Theorem 10.6.3,
p. 285 (PDF p. 297). The paired local modules give the proof details and
exact citations.
