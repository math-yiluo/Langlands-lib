# Residue-normalized determinant scaling for additive Haar

`residueAbsoluteNNReal` packages the Library's residue-normalized
absolute value in the nonnegative real codomain used for measure
scaling. `map_mul_residueAbsolute` applies the published scalar Haar
law with the uniformizer of order one. The normalized valuation of
this uniformizer is the exponential of −1, so its powers account for
the values of all nonzero elements. The residue normalization gives
the prescribed value at the uniformizer and value one on integral
units.

`ResidueNormalizedHaarScalingStatement` gives the determinant scaling
for a continuous linear automorphism of a finite-dimensional Hausdorff
topological vector space over the local field. The proof chooses a basis
and writes the automorphism as a matrix in those coordinates. Additive
Haar scales by the inverse residue-normalized absolute value of that
matrix's determinant, which equals the determinant of the original map.
This internal specialization of the Library's scalar and matrix Haar
laws gives the normalization used in the local Weyl charts.
