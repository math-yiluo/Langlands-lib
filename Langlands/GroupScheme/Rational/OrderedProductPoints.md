# All-test coordinates and point formulas for ordered multiplication

This is internal categorical infrastructure for the exact ordered-product
target in `Rational.RootProductStatement`. It uses the actual group laws and
the categorical finite product from `Rational.WeightSemigroup`. The point
formula signatures originated in Worker 1313's central-extension descent
draft; Worker 362 implemented this module and the coordinate comparison.

`finiteProductIsLimit` and `finiteProductPointsEquiv` derive the underlying
product fan and its multiplicative point equivalence directly from preservation
of finite products by the forgetful functor from group objects. The finite
index type has a universe independent of the base-scheme universe. In
particular, `Fin n` works over any `Scheme.{u}`. These declarations extend the
index-universe scope of the existing `GroupScheme.piPointsEquiv` without
changing it. Projection and both directions of naturality hold on every test
scheme, including the empty product.

`orderedPoints j x` multiplies the included family of points in `Fin n`
order. `comp_orderedMultiplication` identifies evaluation of the actual
scheme map with this expression. The inverse-coordinate formula records the
same identity for an assembled family. `orderedPoints_naturality` proves
compatibility with arbitrary changes of test scheme, and `orderedPoints_map`
proves compatibility with a commuting family of group-scheme homomorphisms.
The proofs distribute composition through list multiplication using the
actual point group laws. No commutativity is assumed.

`isIso_orderedMultiplication_iff` applies Yoneda's isomorphism criterion after
the coordinate equivalence: the actual scheme map is an isomorphism if and
only if ordered factorization is bijective on every scheme over the base.
The final theorem rewrites this as existence and uniqueness of each ordered
factorization. These are equivalences, not assertions that a given family
satisfies the criteria. They do not prove representability of any subgroup,
cross-exclusion consequences, local lifting, or the CGP product theorem.

The provenance is a derivation from the Library's actual finite product,
its existing ordered multiplication definition, and the categorical Yoneda
criterion in Mathlib. The intended geometric application is the final
fppf-sheaf diagram chase in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), Theorem 3.3.11 and its proof, printed pp.114–116
(PDF pp.140–142), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. No extra geometric input from
that source is used in these categorical lemmas.
