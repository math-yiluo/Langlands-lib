# Proportionality from symmetry of regularized pairings

The argument implements the Hilbert comparison after equation (3.3) in
Shalika (1974), pp. 184–185, for complex-linear regularizations in a
topologically irreducible unitary representation. The common test space
carries the conjugate-linear kernel symmetry and the translates used by the
two regularizations.

Choose an orthonormal Hilbert basis and conjugate its coordinates. This
transports the conjugate Hilbert action back to the original carrier and
reverses the two arguments of the inner product. A nonzero regularization
has dense image because its image closure is an invariant subspace. The
pairing identity and density then give bounded intertwiners sending each
regularization to the same conjugated reference regularization.

Write these intertwiners as `T₀` and `T₁`. Unitarity makes `T₁†` an
intertwiner in the reverse direction. The two products `T₁† T₁` and
`T₁† T₀` therefore commute with the original representation and are
scalar. The first scalar is nonzero whenever the second regularization
is nonzero. Applying the two products to the respective regularized
vectors gives proportionality.
