# Closed-embedding independence of full adelic growth conditions

`Langlands.Automorphic.GroupSchemeFunctions.ClosedImmersionAdelicGrowthIndependenceStatement`
is a proposition target for the existing full adelic growth predicates. Fix any
number field `F` in an arbitrary universe, an actual affine group scheme `G`
over `Spec F`, positive natural ranks `N` and `M`, and matrix representations
`rho : G -> GL_N` and `sigma : G -> GL_M`. Both representations must be
scheme-theoretic closed immersions, using `GroupScheme.IsClosedSubgroup`.
The target asserts the following two families of equivalences.

For every element `f` of the original `ContinuousRationalFunctions F G`,
ordinary moderate growth with respect to `rho` is equivalent to ordinary
moderate growth with respect to `sigma`. The same equivalence is asserted for
the natural-exponent polynomial-growth predicates. These are exactly
`HasAdelicModerateGrowth` and `HasAdelicPolynomialGrowth` from
`GroupSchemeAdelicGrowth`; they bound the unchanged function at every actual
full adelic argument.

For every natural relative dimension `d`, every original smooth structure
`hsmooth : SmoothOfRelativeDimension d G.X.hom`, every explicit scalar
commutator premise `hcalc : AdelicDifferentialCommutator F G hsmooth`, and
every `f` in the original `FinitePlotSmoothRationalFunctions F G`, the
corresponding uniform moderate-growth predicates for `rho` and `sigma` are
equivalent. The same equivalence is asserted for uniform polynomial growth.
Both sides use the identical `hsmooth`, `hcalc`, tangent enveloping algebra,
and `adelicEnvelopingAction` from `GroupSchemeAdelicUniformGrowth`.
The ordinary family requires no smoothness or scalar commutator premise.
No reductivity, connectedness or splitness hypothesis is imposed.

## Bounds and unchanged carriers

The real-exponent predicates use exactly `adelicSourceNorm`, the product of
the local matrix/inverse-entry maxima over all places, with the existing
normalized absolute values and infinite-place multiplicities. Their constants
are strictly positive. The natural-exponent predicates use the existing
dimension-scaled `adelicHeight`, with nonnegative constants. Positive rank
retains the fixed positive scaling factor and the lower bound one for the
scaled height. The already proved real/natural conversion theorems do not
establish independence of the representation by themselves.

For uniform growth, one exponent is chosen before **all** enveloping
elements; only the bounding constant may depend on the enveloping element.
The target retains this quantifier order in both directions by referring to
the existing predicates. It changes neither the function nor the differential
operator. The underlying continuous carrier remains rational-left-invariant,
with positive right action `R(g)f(x) = f(x*g)`. The finite plot-smooth carrier
still requires smooth infinite slices and one common open finite stabilizer.

## Source and derived scope

Getz and Hahn, *An Introduction to Automorphic Representations* (2024),
equations (6.3)–(6.4), printed pp.158–159 (PDF pp.172–173), construct the
inverse-inclusive norm. Equations (6.7)–(6.8) and Definition 6.3.1, printed
pp.161–162 (PDF pp.175–176), give the full adelic product and the ordinary
and uniform bound quantifiers. Exercise 6.1, printed pp.179–180
(PDF pp.193–194), asks for equivalence of norms from two faithful
representations of a reductive group over a global field, for any finite or
infinite set of places, and for the resulting growth independence.
The complete retained author errata, especially Chapter 6 on p.2, makes no
correction to these formulas, Definition 6.3.1 or Exercise 6.1.

This target is an internally derived extension of that consequence to the
Library's affine group schemes over number fields, its explicit closed
embeddings, its scaled natural-exponent bounds and its original function
carriers. In particular, GH (6.1), printed p.158 (PDF p.172), uses an algebraic
tensor product for smooth adelic functions. The finite plot-smooth carrier
here imposes no global finite-tensor condition. Uniform independence is
asserted for the extended bound predicates on that carrier; it does not
identify the carrier with the literal GH smooth space.

A prospective proof can apply
`RepresentationGrowth.ClosedImmersionAdelicHeightDominationStatement`
in both directions. A bound `H_sigma <= A * H_rho^e`, with `A` and `e`
independent of the point and the enveloping element, transfers a
natural-exponent bound for `H_sigma` to one for `H_rho`. For uniform growth,
the new exponent is the product of the original shared exponent with `e`,
chosen before the enveloping element; each derivative constant absorbs
`A` to the original shared power. The existing real/natural conversion
theorems would then give both real-exponent equivalences. This is a proposed
derivation, not an invocation of an assumed domination theorem.

## Boundary

This file defines only the proposition. It proves none of the equivalences
and assumes no proof of full adelic height domination. The earlier
`GroupSchemeGrowthIndependence` concerns bounds separately on finite adelic
slices and does not establish this full adelic target. Equality of the
corresponding subspaces and function-preserving comparison maps remain
consumers of a future proof. No automatic uniform growth, literal tensor
comparison, full infinite-translation stability of the uniform space,
properness, reduction theory, finite volume or square integrability is
asserted.
