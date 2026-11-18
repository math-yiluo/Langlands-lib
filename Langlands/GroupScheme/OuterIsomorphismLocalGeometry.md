# Local parameters of an outer-isomorphism quotient

Worker 592. Internal derived material from the exact all-test orbit condition
of `OuterIsomorphismScheme` and the published local normalized-family API.
The acting group is assumed flat and locally of finite presentation.
An outer quotient is supplied; existence of that quotient, or of its Isom
source, is not asserted here.

A complete family of local orbit representatives consists of a parameter
scheme `M`, its projection to a local base `U`, and a family of actual
isomorphisms on `M`. Unique decomposition on every original-base test says
that the orbit family `A × M → I × U` is an isomorphism. The module proves
that `M` is isomorphic to `O.parameter × U`, preserving its projection to
`U`. Thus the same comparison gives an actual isomorphism over `U` from
the pullback of the outer parameter to `M` viewed as a scheme over `U`.
In particular a locally constant normalized parameter determines the
scheme-level local constancy of any supplied exact outer quotient.

The Lean proof compares two locally surjective presentations on `I × U`:
the given outer class map with its extra base parameter, and the class map
from the normalized-family product coordinates. Both are flat, surjective,
and locally of finite presentation. The comparison accepts a proof of local
finite presentation for the actual outer class map and pulls it back along
the product projection. The default uses fpqc property descent from the
acting group. The two class maps have the same sectionwise kernel by the
actual orbit equations. The common-kernel sheaf theorem identifies their targets.
Full faithfulness of the scheme Yoneda functor recovers an actual scheme
isomorphism. Epimorphism cancellation proves preservation of the base
projection, and the product pullback comparison puts the result in `Over U`.

Every base scheme and universe is retained. The test schemes and the
normalized parameter may be disconnected, nonaffine, or non-quasi-compact.
No separatedness or finiteness condition on the outer scheme is needed.

`localParameterIso` selects an actual slice-category isomorphism from the
proved existence result, for use by constructions requiring explicit data.
