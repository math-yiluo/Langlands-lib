# Orthogonal block extension of affine Clifford lift schemes

`Langlands.GroupScheme.CliffordSpin.CliffordSpinAffineBlockExtensionStatement`
gives a homomorphism from the affine Clifford lift group of \(Q\) to that of
the orthogonal sum \(Q\perp P\). The target basis is the concatenation of the
given finite bases. The characteristic assumption is that two is invertible
in the base field.

On any commutative coefficient algebra, `orthogonalExtension` maps the
Clifford unit through the tensor extension of the Clifford algebra inclusion
and sends its action matrix to the block diagonal matrix with identity on
the second summand. The inclusion preserves grading and reversion. Its even
elements commute with the second vector summand, so the intertwining
equations on that block hold with identity action. The first block equations
follow by applying the Clifford inclusion to the original equations. The
block extension preserves determinants, and both coordinate operations
commute with arbitrary coefficient maps. Corepresentability then gives the
group-scheme homomorphism and its stated action on affine points.

The construction formalizes the block inclusion used for the spin
stabilizer in Kneser, *Lectures on Galois Cohomology of Classical Groups*
(1969), §§5.9–5.10, pp. 93–95.
