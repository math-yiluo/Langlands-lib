# Exact pullback of closed facets

This is internal derived content from the existing sign definitions of affine
facets and their closed-side closures. It introduces no literature translation.

For arbitrary real affine torsors, membership of `y` in the closed facet through
`x` is equivalent to membership of `lineMap y x t` in the facet through `x` for
every `0 < t ≤ 1`. The forward implication checks each affine root value, which
is `(1 - t) * ψ y + t * ψ x`. The reverse implication takes the limit of this
real expression at positive parameters tending to zero. A positive root value
at `x` forces a nonnegative value at `y`, and a negative value forces a
nonpositive one. A zero value at `x` forces zero at `y` by the midpoint formula.
No topology on either affine torsor is assumed.

Affine maps preserve these parametrized segments. Consequently, exact pullback
of the facet through the image of a point implies exact pullback of its
closed-side closure. The conclusion holds for arbitrary sets of affine
functionals, without root-system, dimension, or injectivity assumptions.

The segment criterion and its forward implication are reused from [FacetClosurePullback](FacetClosurePullback.md). This module adds `preimage_facetClosure_eq_of_preimage_facet_eq`, whose hypothesis is the open-facet pullback identity at the specified point.
