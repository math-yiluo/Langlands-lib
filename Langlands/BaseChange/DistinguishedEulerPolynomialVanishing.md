# Vanishing of separated distinguished Euler denominators

`DistinguishedEulerFromEquationsStatement` takes a natural number `q > 1` and
compares two completed equations whose forward and dual finite Euler products on
a right half-plane differ by evaluations at `q⁻ˢ` of two polynomials with constant
term one. The lower product is the upper product multiplied by the corresponding
polynomial evaluation. Assume the total epsilon
multipliers are continuous and nowhere zero, and the forward polynomial roots are
separated from the reflected dual roots under `x ↦ q⁻¹ / x`. Then both polynomials
are one.

The proof continues the two finite-product relations meromorphically. It clears the
Gamma denominators in the completed equations and cancels the common dual finite
product, which is nonzero on a right half-plane. The cleared relation is continuous,
so its germ equality holds pointwise.
For every nonzero spectral value, adding imaginary periods realizes that value at
points with arbitrarily large imaginary part. Each shifted real or complex Gamma
block has its poles on a single horizontal line. At a point above a hypothetical
forward root, the relevant Gamma denominators are nonzero, and separation makes the
dual polynomial nonzero. The cleared equation gives a contradiction. With the forward
polynomial equal to one, evaluating over a reflected dual root gives the same
conclusion for the dual polynomial. The constant terms determine their value.

`DistinguishedEulerPolynomialVanishingStatement` carries out the last step
directly from the cleared equality and the same bound, polynomial normalizations,
nonvanishing multipliers and root separation.

This is an internal analytic alternative for the Euler comparison at the
distinguished place in Arthur–Clozel, Chapter 1, proof of Proposition 6.9(ii),
printed p. 70 (PDF p. 84). It uses the local polynomial separation directly.
