# Compact Gram cutoffs for complex Godement sections

`ComplexGodementGramCutoffStatement` starts from a smooth upper standard
module vector. Cut off its normalized rectangular function by a smooth
function of the row Gram matrix, supported in a compact subset of the
invertible square matrices. The result is a smooth compactly supported
test whose support lies in the full-row-rank locus. The real trace of a
row Gram matrix bounds each squared entry norm, which gives compactness
of the cutoff support. Inversion of the Gram matrix supplies a right
inverse for each rectangle in its preimage.

The corresponding section on the unitary subgroup is an integral of
lower-block translates of the original vector, weighted by the cutoff,
the smaller input at the inverse, and the half power of the normalized
absolute value of the smaller determinant. The normalization follows by
cancelling the two determinant characters in the descended function.
Unitary invariance of the Gram matrix removes the larger compact
variable from the cutoff.

This is an internal step toward the upper-Borel form of Jacquet (2009),
§7.1, Proposition 7.1(v). It adapts the Library's real Gram cutoff.
