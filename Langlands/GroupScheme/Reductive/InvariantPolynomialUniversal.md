# Universal polynomial identities and epimorphic subgroup products

This is an internal algebraic construction for the Haboush proof. It uses the
existing `MatrixRepresentation`, `scalarMap` and `IsInvariantPolynomial`
definitions without changing them. No reductivity, geometric reductivity,
Steinberg-module existence or characteristic hypothesis enters the universal
identity and product-detection lemmas.

For an arbitrary commutative base ring `R : CommRingCat.{u}`, a finite coordinate
type `n : Type` and an actual representation `ρ`, `actionPolynomial ρ g F` is the
polynomial over the global sections of the source of `g` obtained by extending
coefficients of `F` and substituting the linear forms of the point matrix
`ρ(g)`. Its evaluation is exactly the evaluation of `F` on `ρ(g) x`.
`map_linearPullback` and `actionPolynomial_naturality` show that these
polynomials commute with change of coefficients and relative test maps.
`linearPullback_mul` and `actionPolynomial_mul` record that polynomial
substitution reverses the order of composition of the linear maps.

`isInvariantPolynomial_of_universal` proves that equality of this transformed
polynomial with the coefficient extension of `F`, at the identity point of the
acting group scheme itself, implies the original all-test-scheme invariance.
The proof pulls the polynomial equality back along an arbitrary group point,
then evaluates at an arbitrary section-valued vector. This implication needs no
affineness assumption on the group.

For the reverse direction, `IsInvariantPolynomial.affine` first transports the
original equation on an affine test scheme through the canonical affine
section algebra equivalence. `affine_polynomial` then tests it over the
polynomial algebra of the coefficient algebra, at the generic vector of
variables. Transport through an affine model of the source gives
`IsInvariantPolynomial.actionPolynomial`: on every point with affine source,
invariance implies the polynomial equality. Hence
`isInvariantPolynomial_iff_universal` gives the equivalence when the acting
group is affine. Once that universal equality is known,
`actionPolynomial_of_isAffine` transports it to points with arbitrary source
scheme. These steps do not replace polynomial equality by equality of
functions on field-valued points; nilpotents and all test algebras are retained.

`isInvariantPolynomial_of_epi_polynomial` assumes a point whose underlying
scheme morphism is an epimorphism and the polynomial equality at that point.
It reflects the equality back to the universal point, using injectivity of
pullback on global sections and of the induced coefficient map on
multivariate polynomials. The original all-test invariance then follows from
the universal implication. The source need not be affine for this direction.
There is no base change of the epimorphism in this argument.

The main product result
`isInvariantPolynomial_of_epi_subgroupProductMap` takes two actual
homomorphisms `i : Z ⟶ G` and `d : D ⟶ G`, affine source group schemes `Z` and
`D`, and an epimorphism `subgroupProductMap i d` in schemes over the base. A
polynomial invariant under both restricted representations is invariant under
`G`. The two universal identities pull back along the projections of the
product, and the substitution-composition identity combines them. The
forgetful functor from schemes over the base supplies the underlying scheme
epimorphism required by coefficient reflection. The ambient group need not be
affine for this product result, and neither centrality nor a derived-subgroup
hypothesis is required. The companion `iff` includes the two immediate
restriction implications.

Finally, the `CentralZeroWeight` lemmas apply this criterion over an arbitrary
field `k : Type u` to representations indexed by `Fin N`. Their additional
inputs are an affine ambient group, an affine group `D`, a central homomorphism
`j` from a specified finite split torus, a homomorphism `d : D ⟶ G`, and an
epimorphic multiplication map. If a supplied polynomial is invariant under
`D`, pulling it back by the zero-weight projection makes it invariant under
`G`. The split torus is affine by its existing construction. The final
`linearPullback_separator_of_epi_product` also assumes a torus-fixed vector,
a supplied homogeneous degree and nonzero evaluation; it proves that the same
pullback retains that degree and nonzero evaluation. In particular, a supplied
positive degree stays positive. It does not construct the initial separator or
assert that a suitable central product exists.

The provenance is internal: the arguments combine polynomial substitution and
coefficient injectivity from Mathlib with the actual representation naturality,
affine section comparisons, global-section injectivity along epimorphisms and
zero-weight projection API already in the project. They prove elementary
transport and assembly lemmas. Existence of the required subgroup product,
the simply connected positive-characteristic separator and the final Haboush
proposition remain separate proof obligations.
