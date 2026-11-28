# Compact-adapted rational matrix heights

`rationalCompactHeightAdaptation` proves
[`RationalCompactHeightAdaptationStatement`](RationalCompactHeightAdaptation.md).
Compactness in the canonical topology on the rational points gives algebraic
boundedness. The theorem `boundedSubgroupStableLattice` then gives a full lattice
preserved by the supplied compact subgroup in the original representation.
A basis of the lattice over the valuation ring extends to a basis over the
local field.

The proof uses `basisCoordinatePoint` to take the matrix carrying vectors to
their coordinates in the extended basis as an actual rational point of the
same general linear group. The corresponding inner automorphism preserves
the closed immersion. For each element of the compact, the columns of its
conjugated matrix are the coordinates of the images of lattice basis vectors.
Those images lie in the lattice, so the coordinates belong to the valuation
ring and their residue-normalized absolute values are at most one. Subgroup
inversion gives the same bound on the inverse matrix. These two bounds give
the asserted inclusion in `rationalHeightSubgroup`, so the existing
`rationalHeight_mul_mul` theorem gives bi-invariance under the supplied compact.

Waldspurger (2003), I.1, printed p. 242 (PDF p. 8), chooses an embedding in
which the compact maps into the integral general linear group and defines the
height as the logarithm of the maximum of the absolute values of the matrix
entries and inverse entries. The stable-lattice argument supplies the basis
change in that choice. The registered source is `waldspurger-2003-plancherel`
with SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
[DOI 10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
