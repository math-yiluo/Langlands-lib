# A regular point of the torus Lie slice over the ground field

`RegularTorusLieSliceStatement` concerns a homomorphism from a torus to
an affine group scheme locally of finite type over an infinite field,
with finite Lie coordinates. It gives a left inverse of the torus Lie
centralizer basis matrix and a parameter where the bracket matrix plus
the associated projection is invertible.

The columns of `torusCentralizerMatrix` form a basis of the common kernel
of the torus adjoint differentials. The basis matrix has a left inverse
`D`. If the basis matrix is `B`, then `B * D` projects onto this common
kernel.

Over a splitting field, the regular Lie vector supplied by the torus
weight spaces has coordinates `B *ᵥ t`. Its bracket matrix `M` kills
`B`, and the images of `M` and `B` span the ambient Lie coordinates.
Given a decomposition `M *ᵥ x + B *ᵥ y`, a preimage under `M + B * D`
is `x - B *ᵥ (D *ᵥ x) + B *ᵥ y`. Thus the determinant is nonzero at the
splitting-field parameter. It is the evaluation of a polynomial over the
ground field, obtained by using the adjoint matrix with polynomial
coordinates and then taking the determinant. Naturality of the finite
coordinates and tangent matrix gives the evaluation formula. A nonzero
polynomial over the infinite ground field has a nonzero value there, so
the sum of the bracket matrix and the projection is invertible at some
ground-field parameter.

This is a finite-coordinate regularity argument for the Lie slice used
in Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994),
Theorem 2.18, printed pp. 104–105.
