# Closed compact-orbit containment of the actual weighted average

Author: Worker 94.

This internal proof development uses compact restrictions of genuine
derivative coordinates. Each restricted continuous-function space is
a Banach space, and finite products of these spaces are Banach spaces.
The derivative topology is induced by all these coordinates.

An integral of an integrable Banach-valued function taking values in a
closed complex submodule stays in that submodule: the continuous
quotient map commutes with integration and sends the integrand to zero.
Membership in a product closure can be checked on all finite collections
of coordinates, by the finite-coordinate neighborhood basis.

`finiteOrbit_integrable` integrates the weighted actual compact orbit
after applying any finite collection of compact derivative restrictions.
Joint continuity of the compact action and compactness of its domain
give integrability in that finite Banach product. Composing the integral
with the continuous projections and point evaluations, and using
`envelopingDerivative_average`, identifies it with the same finite
coordinates of `averageCLM`.

Every integrand belongs to the closure of the image of the complex
compact-orbit span. The closed-submodule integral argument therefore puts
these finite coordinates of the average in that closure. The generic
finite-coordinate closure lemma and the inducing compact-coordinate map
give `average_mem_closed_compactOrbit`: the actual average belongs to
the closed complex span of the actual compact right orbit.

The proof uses vector integration only in finite products of Banach
spaces. It requires no completeness of the smooth carrier and no
locally convex integral there. This is an internal derived argument
using the actual derivative topology and actions. It establishes no
character projector, admissibility, reproduction or automorphic growth.
