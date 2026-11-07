# Canonical big-cell data from a supplied highest-weight representation

This internal construction by Worker 1369 composes the published
`HighestWeightExtremal` and `CanonicalRhoBigCell` constructions. It supplies
the first six laws of the Steinberg big-cell conclusion from a highest-weight
representation at integral rho. It does not prove `SteinbergBigCellStatement`.

Fix an algebraically closed field `k : Type u`, an affine group scheme `G`,
a supplied split pinning `p`, a finite root index and the integral coroot-span
condition `hspan`. Write `r = IntegralWeylVector.rho p.rootDatum p.base hspan`,
`nu = p.rootDatum.Polarization r`, and `lambda = groupHom nu ≫ p.inclusion`.
Supply `BorelTorusBruhatCovering` for the actual affine dynamic parabolic
of `lambda` and the original torus inclusion.

The primary definition `SplitPinning.highestWeightBigCellGeometricData`
also takes an actual `MatrixRepresentation G n` on an arbitrary finite small
index type and its explicit `p.IsHighestWeight` certificate at `r`. It returns
`SteinbergBigCellGeometricData G`: actual subgroup and torus maps, an opposition
point and two coordinates, together with left and inverse right covariance,
value one at the identity, the nonzerodivisor property, factorization at every
point where the group coordinate is a unit, and the diagonalizable lift for
every common point of the two subgroup maps. Every test scheme remains
unrestricted; nonaffine, nonreduced and empty tests are included.

The proof uses `negativeRhoExtremalRepresentationData` to construct the actual
conjugated-dual representation, its integer exponents, its unique minimum
index, its canonical cocharacter equality and its negative-rho torus entry.
It passes these witnesses and their three laws to
`IsRootDatumOf.canonicalRhoBigCellGeometricData`. The supplied pinning provides
connected reductivity, the split maximal torus, its actual reduced root datum
and its base. No structural existence assertion is inferred.

The projection lemmas identify the diagonalizable subgroup with the standard
diagonalizable presentation of the original torus inclusion, the subgroup map
with `Affine.parabolicHom lambda`, the opposition point with the root-datum
opposition representative, the weight coordinate with the actual
`Dynamic.negativeRhoCoordinate`, and the group coordinate with the distinguished
matrix coefficient of the constructed conjugated-dual representation.
In particular, the subgroup and weight coordinate are the canonical objects
independent of the chosen highest-weight representation.

`highestWeightBigCellData` takes, as an additional explicit premise, the exact
remaining law for this canonical parabolic and this negative-rho coordinate:
for cofinally many exponents, the entire left covariant coordinate subspace
has a finite basis on which the actual right regular representation is
rationally irreducible. It applies `withIrreduciblePowers`, preserving all
witnesses and coordinates. No cyclic subspace replaces the entire subspace,
and no finite-dimensionality or irreducibility theorem is proved here.

`isDominantWeight_rho` derives dominance from the proved value one on every
simple coroot. `highestWeightBigCellGeometricDataOfDominantExistence` specializes
an explicitly supplied `SplitDominantHighestWeightRepresentationsExistStatement`
at this dominant character, chooses the resulting representation and applies
the primary constructor. The existence statement is a premise of this
conditional definition, not an invoked theorem.

The provenance is an internal derivation from the imported Library results;
no external source is cited. Split pinning, integral coroot span, highest-weight
existence, Bruhat covering and the entire-space seventh law remain separate
obligations for the exact host target. No characteristic assumption is needed
for these conditional constructions.
