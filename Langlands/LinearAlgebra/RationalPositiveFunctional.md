# Rational functionals preserving finite strict positivity

This internal linear-algebra consequence concerns an arbitrary rational vector
space and a finite indexed family of its vectors. If a rational-linear map to
the reals is strictly positive on that family, a rational-valued linear
functional is strictly positive on the same family. The second theorem also
retains exact vanishing on a specified rational subspace.

The proof chooses a basis of the rational vector space. The coefficient
families giving strict positivity on every test vector form an open subset
of the product of copies of the reals: each vector has finite basis support,
and there are finitely many strict inequalities. The given real-valued
functional supplies a point of this open set. Density of rational coefficient
families supplies a rational point, whose basis extension is the desired
functional. No finite-dimensional assumption on the ambient space is needed.
To preserve vanishing, the second theorem applies the first to the quotient
by the specified subspace and pulls the resulting functional back.

The final theorem concerns a closed pointed cone in a finite-dimensional real
vector space with its module topology. For a finite family of vectors in the
cone whose negatives lie outside it, a single supporting linear functional is
nonnegative on the cone and positive on every member of the family. The proof
transports the cone through a finite basis to a Euclidean coordinate space,
separates each negative vector using the closed-cone hyperplane separation
theorem, and sums these finitely many functionals.

The provenance is an internal derivation from basis extension, product density
and the universal property of a vector-space quotient, together with Mathlib's
closed-cone separation theorem. No external literature claim is made.
