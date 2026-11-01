# Detecting simple quotients from centrally separated exact classes

This internal algebraic helper works with an arbitrary coefficient field and
group, with independent coefficient, group and carrier universes. Suppose an
actual finite-length smooth representation `A` has a composition series on
whose simple factors one central group element acts through pairwise distinct
scalars. Every actual finite-length smooth representation `C` with the same
canonical exact Grothendieck class has an actual surjective intertwiner to
each of those graded factors. More generally, a nonzero actual map from `A`
to any irreducible test representation yields an actual surjective map from
`C` to that test representation, whose carrier may have an independent
universe.

The hypothesis about distinct central scalars is explicit. Equality of exact
classes alone does not transfer quotient maps for arbitrary finite-length
representations. The quotient retains all actual short exact sequence
relations, including nonsplit ones; no admissibility or finite dimension over
the coefficient field is assumed.

`centralEigenProjection` evaluates a Lagrange basis polynomial in the action
of the central element and restricts its range to the corresponding actual
eigenspace. The central action and every polynomial in it are actual
intertwiners. The published nodal-polynomial annihilation theorem shows that
the image lies in that eigenspace. The Lagrange polynomial is `1` on its own
node, so the projection is surjective when the scalars are distinct.
`centralGradedProjection` composes with the published equivalence from the
eigenspace to the corresponding actual graded representation and is also
surjective.

`exists_equiv_of_generator_sum_eq` matches the indices of two finite sums of
irreducible generators when one family's labels are distinct. Each label on
either side occurs on the other side, by evaluating the coefficient at that
label and using positivity. Sending every generator to `1` equates the two
cardinalities. Choosing matching indices, injectivity of the first label
function gives surjectivity of the match, and equal finite cardinalities make
it a bijection.

For the exact-class detection theorem, choose an actual composition series
of `C` and apply the published exact factor map to the class equality. The
distinct central scalars make the labels of the supplied series of `A`
distinct: an equivalence between two simple factors would force their
scalars to agree on a nonzero vector. Matching finite label sums therefore
provides a bijection between the two series' factors. It transfers the
distinct scalar actions to the chosen series of `C`. Its central graded
projection, followed by the actual equivalence of matching simple factors,
is the required surjective intertwiner.
For the irreducible test-object form, the published simple-map multiplicity
detector gives positive multiplicity of the test object in the supplied
series of `A`. Thus one actual graded factor is equivalent to the test
object, and composition with that equivalence gives the claimed surjection.

The substantial project inputs are
`Smooth.IrreducibleCompositionFactors`, for genuine simple labels, canonical
factor sums, actual composition series and their descent through every exact
relation, and `Filtration.CentralEigenspaceSplitting`, for polynomial
annihilation of filtered central actions and actual equivalences of
eigenspaces with the corresponding graded factors.
`Filtration.SimpleMapMultiplicityDetectionProof` supplies positive actual
composition-factor multiplicity from a nonzero map to a simple test object.
Mathlib supplies
Lagrange interpolation, polynomial evaluation in endomorphisms, and finite
cardinality arguments. The provenance is the internal combination of these
generic algebraic constructions. No literature assertion is transcribed,
and there is no Aubert, parabolic or classification theorem input.

Author: Worker 1186.
