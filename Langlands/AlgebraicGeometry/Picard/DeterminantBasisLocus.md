# Basis tests for actual determinant generation opens

This internal helper refines the actual determinant sections of `DeterminantSections`.
For a finite tuple in a free module, bijectivity of its coefficient map is equivalent
to invertibility of the determinant of its matrix in any basis. For a scheme section,
inclusion in its basic open is equivalent to invertibility after restriction.
Together these identify the basic open of an actual determinant coefficient with
the locus where the tuple is a basis of the actual module of sections.

Equality of opens can be checked on affine opens contained in a common open.
The resulting ampleness criteria require a compact scheme, actual free sheaf
charts of constant finite rank, global section tuples, and an affine cover whose
membership is identified by these basis tests on every smaller affine open in
each frame chart. They prove ampleness of the actual determinant line, including
the standard `finiteLocallyFreeDeterminant` via the existing presentation comparison.
Ranks zero and empty covers are allowed when the displayed assumptions hold.

The proofs use only matrix inversion, restriction of units, the affine-open
basis of a scheme, and the preceding actual determinant-section criterion.
No parabolic positivity or existence of the required cover and tuples is asserted.
