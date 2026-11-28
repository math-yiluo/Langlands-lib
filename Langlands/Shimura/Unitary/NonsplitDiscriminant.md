# The discriminant at a nonsplit finite place with a split algebra

For a degree-\(2m\) unitary pair over a CM extension with \(2m>0\),
supply an `EvenDiscriminantPresentation` and the place embeddings
used to define the local invariant. At a nonsplit finite place,
assume the upper completed algebra has zero Brauer invariant.
`localInvariant_discriminant_at_nonsplit` computes the resulting
discriminant invariant using the actual unique quadratic upper
completion. The signed determinant is the unit returned by
`nonsplitSignedDeterminant` for the Hermitian chart of the actual
completed involution.

The unique-place completion automorphism extends CM conjugation and
agrees with the coefficient involution in the chart. The completed
center equivalence specifies its action on scalars in the matrices.
The transported discriminant therefore vanishes precisely when the
signed determinant belongs to the actual norm subgroup. Its double
vanishes, so its invariant is \(0\) on the norm subgroup and \(1/2\)
in \(\mathbb Q/\mathbb Z\) otherwise. The two number field universes
are independent.
