# Numerical norm filtration in finite abelian extensions

`FiniteAbelianNormUnitImageCardinality.{u,v}` asserts that for every finite
abelian extension of actual p-adic fields `E/F`, the image of `U_F^ceil(a)` in
the actual quotient `Fˣ / N_{E/F}(Eˣ)` has order equal to the upper ramification
group `Gal(E/F)^a`, for every real `a ≥ 0`. Here `ceil(a)` is the natural
ceiling, `U_F^0` is the full integral unit group, and positive unit levels are
the actual congruence subgroups. The fields may live in independent universes.
The assertion covers every compatible choice of the base and extension
topological data.

The quotient uses the determinant norm image, and the upper group uses the
published inverse Herbrand function on the supplied integer ring. The
finite-dimensional instance is inherited from the finite-dimensional
extensions of `Q_p`. No reciprocity homomorphism or character is mentioned.
This file states the numerical theorem; it does not prove it.

This is a derived formulation of Serre, *Local Fields* (1979), Chapter XV,
§2, Theorem 1 and Theorem 2, printed pages 227–228 (PDF pages 232–233).
For a totally ramified abelian extension, the norm-index recursion and the
graded norm injection of Theorem 1 give the equality at integer upper levels.
Theorem 2 extends it to a general abelian extension using the inertia fixed
field and surjectivity of the unramified norm on units. The Hasse–Arf
integrality conclusion in Theorem 1 makes the upper group constant between
successive integer upper levels, with the ceiling convention used here.
Equivalently, the numerical equality follows from the filtered reciprocity
isomorphism in Corollary 3 and its general-extension version. Inverting a
reciprocity map preserves all subgroup orders, so its normalization has no
effect on this statement.

The source is registered as `serre-1979-local-fields`, content SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
This numerical assertion is an arithmetic prerequisite for deriving literal
unit-image equalities from norm kernels and restriction compatibility.
