# Frobenius cutoff along actual root curves

This is derived supporting work by Worker 1369. It combines actual affine
coordinate evaluation, normal Frobenius-origin subgroups, polynomial Frobenius
descent, and the actual curve-polynomial construction. It introduces no
external source assertion.

Let k be a field in any universe, let p be its exponential characteristic,
let r be any natural number, and put q = p^r. The group schemes appearing in
the coordinate constructions are affine over Spec k. All relative test
schemes are allowed, including nonreduced and empty schemes.

## Actual coordinate pullback and curve comparison

`schemePullback G H a` is the k-algebra homomorphism from the actual coordinate
algebra of G to that of H induced by any relative scheme morphism
`a : H.X ⟶ G.X`. It uses actual point evaluation on H and the inverse global
coordinate equivalence. `pointAlgebraHom_schemePullback` proves that evaluating
this pullback at any test point h equals evaluating the original coordinate at
h followed by a.

`isOriginTestPoint_map` proves that every homomorphism of affine groups maps
intrinsic height-r Frobenius-origin points to intrinsic origin points. The
proof uses the characterization by equality of q-th powers of all actual
coordinate evaluations with their identity values, together with the actual
coordinate pullback and preservation of the identity.

`additiveCoordinateEquiv` compares the actual coordinate algebra of the
additive line with its one-variable multivariate polynomial presentation.
`curvePolynomial_eq` identifies the earlier actual curve polynomial with
`schemePullback` followed by this equivalence and the standard univariate
polynomial equivalence. `curvePolynomial_schemePullback` proves compatibility
with restriction along a relative scheme morphism. `negativeCurve_comp` proves
the corresponding compatibility for translated curves under a group
homomorphism.

## Origin invariance and the strict degree cutoff

Suppose an actual coordinate b on G is right invariant under every intrinsic
height-r Frobenius-origin point on every relative test scheme. Fix a
homomorphism xm from the additive group to G and a rational point g of G.
`negativeCurve_originInvariant` proves that the actual pullback of b along
the curve s ↦ xm(s)g is origin invariant on the additive group. Indeed, adding
an origin point h to s changes xm(s)g on the right by
`g⁻¹ xm(h) g`; the mapped origin point remains an origin point by normality.
This uses the actual point-group laws, without an additive presentation of G.

`negativeCurve_exists_expand` applies actual polynomial Frobenius descent to
that pullback. The identity `uniqueAlgEquiv_expand` then gives a polynomial Q
such that the curve polynomial is `Polynomial.expand k q Q`. Expansion raises
the variable to its q-th power and preserves coefficients.

`eq_C_of_expand_natDegree_lt` proves that an expanded polynomial P of natural
degree strictly less than q is constant. The expansion degree formula forces
the natural degree of Q to be zero. Applying this to the actual curve yields
`negativeCurve_eq_C`.

Finally, `schemePullback_eq_scalar_of_curvePolynomial_eq_C` transports a
constant curve polynomial back to a scalar in the actual additive coordinate
algebra. `pointAlgebraHom_negativeCurve_eq` therefore proves, for every
relative test scheme V and every additive V-point s, that evaluation of b at
`xm(s)g` equals evaluation at g pulled back to V. The point g is the fixed
rational point throughout this conclusion.

The strict bound is a visible premise; it is not derived in this module.
There is no positivity assumption on r, infinitude or algebraic closedness
assumption on k, or nontriviality assumption on a test's ring of sections.
The constant-polynomial statement includes the zero polynomial. The unit
does not upgrade the rational translate g to an arbitrary test point,
construct a closed translation stabilizer, prove generation by simple root
groups, fixed-height injectivity, the whole-space dimension bound, or
`SteinbergBigCellStatement`. Those remain separate obligations.
