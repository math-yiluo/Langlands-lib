# Full outer geometry from pinned constant charts

Worker 592. Internal derived assembly from the supplied-Isom pinned chart
statement, the actual affine pinned atlas of a reductive group scheme,
and exact-orbit quotient geometry. The pinned chart statement is an
explicit hypothesis and no proof of it is supplied here.

For any supplied full automorphism representative of a reductive group,
and any independently supplied full-centre reductive quotient, the first
theorem proves all of the required geometry of any supplied exact outer
quotient: its parameter is separated and étale, its class map is affine,
the positive inner-automorphism map is a closed immersion, and its parameter
is an actual constant scheme after base change to each member of an
étale cover. The cover is the group's affine pinned atlas.

On each chart, the supplied group's pullback is identified with its pinned
model. The pinned statement gives a complete constant family of local
orbit representatives. The existing local-section change-of-base adapter
expresses this family on every original-base test, retaining its projection
to the chart. Exact-orbit local parameter comparison then identifies the
outer parameter's actual pullback with that constant parameter. Fppf
property descent supplies separatedness and étaleness. Affineness follows
from the affine adjoint torsor, and pulling back the closed outer-class
section through the identity gives the closed positive inner inclusion,
using inversion to account for the inverse-precomposition convention.

The second theorem uses the existing effective quotient construction from
pinned charts to provide the outer quotient and this entire geometry at
once. Both the full automorphism representative and the pinned chart
statement remain inputs. In particular these theorems do not establish
Aut representability by assuming the supplied-Isom chart statement alone.
All universes, bases, relative tests, and possibly infinite outer label
types are retained with no additional restrictions.

`automorphismOuterQuotientOfPinnedCharts` selects the actual outer quotient
from the proved existence theorem. Its hypotheses remain the supplied
full representative and the explicit pinned classification statement.
