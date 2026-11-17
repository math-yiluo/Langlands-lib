# Recognition from an algebraic parent of a finite chart cover

This internal adapter constructs an actual embedded affinoid chart and
full recognition of a finite union of original charts from supplied
algebraic parent data. It does not construct the affinoid parent by
effective finite algebra descent.

Fix actual finite chart gluing data `d`, including its original chart
indices, actual pairwise intersection charts, and their stored bounded
restrictions. `ParentData d` supplies:

- An actual presented affinoid parent algebra.
- Entire bounded restrictions to the original component algebras that
  represent full domains, whose spectrum images cover the parent.
- Equality of the two entire bounded composites on every original
  overlap.
- Exact equality between the spectrum image of each overlap composite
  and the intersection of the two component images in the parent.

No parent chart, spectral embedding, equivalence with the section
equalizer, specialness, or recognition conclusion is supplied. Exact
overlap images are needed: compatibility by itself could identify points
in unrelated parent components. These inputs can be obtained from an
effective algebraic descent output and its full component and overlap
equivalences; this adapter leaves their existence to that algebraic
construction.

Only the literal finite union must be Hausdorff. A theorem derives this
from containment in any supplied Hausdorff subspace, such as a common
open Hausdorff product patch. The ambient analytic space need not be
Hausdorff. The coefficient field, ambient space, and atlas-index
universes are independent.

The bounded component restrictions give the actual bounded map from the
parent algebra into the finite section equalizer. Compose its spectrum
map with the existing canonical map from the finite chart union to
the equalizer spectrum. This constructs the continuous map from the
literal union to the parent spectrum. Its values on every component are
the original restriction comaps.

Component coverage proves surjectivity. If two component points have
the same parent image, exact overlap images supply a point of the
actual original overlap above it. Full represented-domain spectral
injectivity, applied to the two component restrictions, identifies both
points with the two restrictions of that common overlap point. The
original chart restriction equations identify their ambient images.
Thus the constructed map on the literal union is injective.

Compactness of the finite union makes this continuous bijection to the
Hausdorff parent spectrum a homeomorphism. Its inverse followed by the
literal subspace inclusion constructs an embedded parent chart in the
original ambient space. The component chart formulas and the exact
relative image loci follow from this homeomorphism and injectivity.
Together with the supplied full representations and entire bounded
overlap compatibility, they construct `affinoidRealization`.

The existing actual-realization theorem proves specialness, including
overlap tensor admissibility, and all intrinsic recognition conditions.
`recognizedSubset` is the resulting recognized literal finite union,
and `recognitionEquiv` is the constructed full bounded equivalence from
the supplied parent to the canonical recognized algebra. Its chart
formula uses that exact equivalence. No algebra-map equality is inferred
solely from ordinary spectrum points.

The provenance is an internal combination of canonical finite chart
equalizers, full-domain spectral embedding, compact quotient topology
and existing finite-affinoid-realization recognition. It transcribes
no external theorem and asserts no effective algebra descent for an
arbitrary finite chart union.
