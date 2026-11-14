# Function detection by bounded points of split tori

This internal auxiliary module develops function detection on the bounded rational
points of split tori over a valued field with infinite residue field. Its intended
application is to the maximal unramified extension in the descended-apartment
torus comparison.

The implemented first step restricts Laurent monomial characters to tuples of
valuation-one units. The regular-unit existence theorem supplies, for each
positive exponent, a valuation-one unit whose power is different from one.
Thus distinct integer exponent vectors give distinct characters on those tuples.
Linear independence of distinct monoid homomorphisms then proves that a Laurent
polynomial vanishing on every such tuple is zero. This follows the existing
`SplitTorusRationalDetection` argument, with its points restricted to valuation
one. These are derived internal results rather than additional assertions
attributed to the source literature.
