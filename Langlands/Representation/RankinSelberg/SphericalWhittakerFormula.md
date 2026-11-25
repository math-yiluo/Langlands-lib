# Spherical Whittaker torus values

This internal development compares actual normalized spherical Whittaker tests
with the half-modulus weighted dominant polynomial on nonnegative dominant
torus weights. The error is the actual torus sequence minus its identity value
times the polynomial. Equal minuscule recursions, vanishing off dominant
weights and equality at zero let the published partition uniqueness theorem
annihilate this error.

The model comparison retains an arbitrary supplied equivariant functional and
normalized spherical test. The model equivalence for a nonzero functional on
an irreducible representation lifts the test to a fixed vector. The actual
principal-series subquotient Hecke scalars give its coset-sum relations.
The published torus coset reduction turns those relations into the exact
radical-weighted recursion. The conclusion concerns nonnegative dominant
weights; it makes no convergence or integral-evaluation assertion.

The final two interfaces specialize to the published
`IsUnramifiedGenericConstituent`, an additive character of integer conductor,
and every supplied nonzero original or inverse Whittaker functional and
normalized spherical test. They identify the actual value at the canonical
uniformizer torus with `halfModulus` times the published `satakeSchur`, at every
nonnegative antitone integral weight. The inducing tuple is recovered from its
uniformizer values using the unramified-character comparison. Repeated
parameter values are allowed.

The polynomial recurrence `sphericalTorusPolynomial_recursion` is imported from
`SphericalTorusRecursion`, and the model/cell interfaces are published Library
results; this module carries out the partition-recursion uniqueness route
(`eq_sphericalTorusPolynomial_of_recursion`) and implements the error
comparison and these specializations.
