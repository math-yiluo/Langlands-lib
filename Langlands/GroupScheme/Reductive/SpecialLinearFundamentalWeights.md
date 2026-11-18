# Fundamental weights of the actual special-linear diagonal torus

This internal calculation uses the published actual diagonal torus of
`SL_{n+1}`, its characters `weightChar`, its coroot formula and the
integral basis `RootDatum.fundamentalWeightBasis`. It is a prerequisite
for identifying the weight in the norm-one Tits normalization.

`coordinateFundamentalChar n k a` is the sum of diagonal characters with
indices from zero through `a`. For a root datum of the actual diagonal
torus, a base numbered by adjacent roots
`weightChar a - weightChar (a+1)` gives these sums pairing with the simple
coroots as the Kronecker delta. The proof uses `typeACoord.coroot'_sum`;
the difference of two indicator coefficients is precisely that delta.
When the integral coroot span is the full cocharacter lattice,
injectivity of the fundamental-weight basis coordinates identifies these
partial sums with the actual integral fundamental weights.

For `SL_{n+2}` (so both endpoint indices exist), the first fundamental
weight is `weightChar 0`, and the last is `-weightChar (last (n+1))`.
The first identity reduces the partial sum to its only summand. The last
uses the published relation that all diagonal characters sum to zero.
Thus these formulas concern actual characters, with the usual adjacent
root numbering, rather than an abstract rational weight space.

The root datum, base and numbering hypotheses in the general lemmas are
supplied by the published `exists_coordinateRootDatum`; they are not
additional existence assumptions. The Prop-valued
`SpecialLinearCoordinateFundamentalWeightsStatement` and its proved
instance `specialLinearCoordinateFundamentalWeights` give precisely this
unconditional existence and every partial-sum formula, also at rank zero.
The endpoint lemmas compute the two
characters used for the standard column representation and its dual.
They do not assert representation-theoretic highest-weight recognition
or a Brauer-class comparison.

Provenance is internal: this is finite integral arithmetic in the
published diagonal-torus coordinates and the defining dual-basis
pairings. It does not introduce a parallel root datum or appeal to a
classification theorem. The field `k : Type u` is arbitrary in every
characteristic, and `u` is arbitrary.
