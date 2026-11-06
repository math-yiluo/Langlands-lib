# Local separation in the actual evaluation topology

Authors: Worker 135, Worker 200 and Worker 712.

The theorem `Langlands.RingTheory.LocalFieldDensity.localSeparation` proves
the published proposition `LocalSeparationStatement.{u,v}`. The field and
algebra universes are independent. For a smooth domain algebra over a
complete nontrivially normed field, every evaluation neighbourhood of an
actual algebra point contains a point at which any given nonzero algebra
element is nonzero. No local compactness or characteristic hypothesis is
used.

This is an internal strengthening of the global separation theorem in
`LocalFieldDensity.Density`. The proof adapts Worker 712's published
`ImplicitPoints.eventually_exists_algHom` argument to retain a prescribed
neighbourhood, and then adapts the localization and algebraicity argument
of `Density.exists_algHom_apply_ne_zero`. It claims no separate assertion
from external literature.

The first helper, `eventually_exists_algHom_mem`, treats a finite submersive
presentation `P` and an algebra map `x`. On the subtype of coordinate
vectors satisfying the defining relations, `pointOfSolution` defines an
actual `AlgPoint`. This map is continuous: presentation surjectivity
expresses each algebra element as a polynomial in the presentation
coordinates, and evaluation of that polynomial is continuous. At the
coordinates supplied by `x`, the constructed point equals `x`. The inverse
image of the given neighbourhood therefore contains a coordinate
neighbourhood `W`.

As in the published implicit-point proof, combine the relation polynomials
and free coordinates into a map `Φ`. Its derivative is invertible. The
Jacobian determinant is a unit at the point, which gives injectivity on
the relation coordinates; the free coordinates and equality of finite
dimensions give a continuous linear equivalence. The inverse function
theorem identifies the image filter of the neighbourhood filter under
`Φ` with the neighbourhood filter at `Φ(x)`. Consequently `Φ '' W` is a
neighbourhood there. Pulling it back along the continuous map that sets
all relation coordinates to zero gives solutions with arbitrary nearby
free coordinates whose associated algebra points lie in the original
neighbourhood.

The second helper, `exists_algPoint_mem_apply_ne_zero`, argues by
contradiction. Localize at an element nonzero at the chosen point so
that the resulting algebra has a finite standard smooth presentation.
The original global implicit-point theorem implies that the map from
the polynomial algebra on the free coordinates is injective: a
polynomial in its kernel vanishes throughout a neighbourhood, hence is
zero by the published polynomial separation lemma.

The given nonzero element remains nonzero after localization. The
published algebraicity lemma
`exists_ne_zero_freeCoordinates_eq_mul` then produces a nonzero free
coordinate polynomial `c` whose image is the product of that element
with another localized element. Precomposition with the localization
map is continuous on actual algebra points and sends the lifted point
to the original point. Pull back the prescribed neighbourhood along
this map and apply the first helper. If the given element vanished at
every point of the original neighbourhood, evaluating the product
identity at these solutions would make `c` vanish on a neighbourhood
of free coordinates. Polynomial separation forces `c = 0`, a
contradiction.

Finally, `localSeparation` applies this second helper to the actual
algebra map underlying the supplied `AlgPoint`. This proves exactly the
local-separation proposition. The later comparison with actual rational
scheme points and the measure and dynamic open-cell arguments are
separate obligations.
