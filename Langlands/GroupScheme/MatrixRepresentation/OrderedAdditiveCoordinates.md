# Coordinate pullback of an actual ordered additive product

Let `G` be an actual affine group scheme over a field `k : Type u`, with
a supplied finite ordered family of group scheme homomorphisms
`x_i : Ga -> G`. This derived unit constructs `coordinateMap x` from the
actual universal ordered point `x_0(X_0) ... x_(d-1)(X_(d-1))`. It is an
algebra homomorphism from the original coordinate algebra of `G` to the
polynomial algebra in `d` parameters.

The vector-group point construction commutes with every map of test
algebras. The published naturality of actual ordered point multiplication
then gives `orderedPoint_naturality`. Applying the published naturality of
point coordinates proves `pointCoordinates_orderedPoint`: on every
commutative test algebra, evaluation of `coordinateMap x` at a parameter
tuple is exactly the coordinate homomorphism of its original ordered
group point. The product at the zero tuple is the identity, so constant
coefficient is the actual identity evaluation.

If this specific coordinate homomorphism is bijective, `coordinateEquiv`
packages it as an algebra equivalence. Under this explicit hypothesis,
`orderedPoint_bijective` proves that every affine point of the original
group has unique ordered parameters over every commutative test algebra
in universe `u`. Its inverse tuple evaluates the original point's
coordinate map on the inverse images of the polynomial variables.
Injectivity follows by evaluating those same coordinate functions.

For every finite matrix representation of `G`, the original universal
matrix pulled back by `coordinateMap x` is precisely the previously
constructed ordered polynomial matrix. Both matrices evaluate at the
actual universal ordered point; evaluating the parameter variables by
themselves is the identity polynomial algebra map.

This is a direct derivation from the Library's actual point-coordinate,
ordered product and universal matrix interfaces. It introduces no new
group law on the parameter space and assumes no commutativity of the
subgroup images. Bijectivity of the actual ordered pullback is an explicit
input, whose existence is not proved here. No root subgroup existence,
Frobenius kernel identification, induced-space equality or Steinberg
irreducibility assertion is made.
