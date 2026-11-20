# Regular parameters of a maximal torus adjoint slice

`RegularMaximalTorusSliceStatement` gives a polynomial nonvanishing locus
in the adjoint slice through a maximal torus of a connected reductive
group over a characteristic-zero field. On that locus, the differential
of the slice at the identity and the chosen parameter is surjective, and
the tangent centralizer of the slice element equals the image of the
Lie algebra of the torus.

The slice matrix spans the common kernel of the torus Lie algebra in
the finite Lie coordinates. This matrix and the negative adjoint matrix
of the slice element form the two blocks of the differential. The
published split-torus regular element makes this polynomial matrix
surjective at a parameter over a splitting field. The determinant of
its product with a variable right inverse is therefore a nonzero
polynomial. Specializing over the infinite ground field and fixing the
right-inverse parameters gives the required polynomial in the original
slice parameters.

Cartier's theorem upgrades tangent centralization by a torus to
centralization on every test scheme. The maximal torus is its own
centralizer, so the slice column space equals its Lie algebra in the
chosen coordinates. This column space lies in the kernel of the
adjoint operator of each slice element. On the nonvanishing locus it
also spans the whole Lie algebra together with the range of that
operator. Rank-nullity gives equality with the kernel.

This internal lemma uses the published regular split-torus slice,
characteristic-zero torus Lie-centralizer theorem and maximal torus
centralizer theorem.
