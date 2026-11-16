# The open ordered cell of the integral Chevalley closure

For reduced finite root data with finitely generated character lattice,
this internal construction identifies the full ordered parameter product
with the pullback of the ambient open matrix cell along the closed
inclusion of the fixed generic Chevalley closure.

The intersection projects openly to the closure, hence flatly. The
`ClosureCell` descent theorem recovers its integral ordered parameters.
Conversely, the actual ordered root and torus product in the closure,
together with its ambient parameter map, defines a map to this
intersection. The two maps are inverse: the closed parameter inclusion
is a monomorphism, and the open intersection projection and closed model
inclusion are monomorphisms. Their exact factorization identities prove
both inverse equations.

`integralCellIso` is the resulting actual isomorphism over the Dedekind
base, and `isOpenImmersion_orderedCellProduct` proves that the full
ordered product is an open immersion into the closure. This is derived
from generic schematic descent and the integral root and torus
factorizations; it asserts neither smoothness nor connectedness of the
whole closure.
