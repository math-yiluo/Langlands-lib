# Bases and actual endomorphisms on local module sections

This internal algebraic prerequisite constructs a genuine module basis on every
open contained in a finite sheaf trivialization. It uses the actual compatible
basis sections and coordinate morphisms from `ModuleDualLocalFree`, rather than
assuming freeness of section modules as extra output data.

For a scheme `X`, an open `U`, an `X`-module sheaf `M`, a finite type `I`, and an
isomorphism from the free sheaf on `I` to `M.over U`, `localSectionCoordinates`
is a linear equivalence from sections on any object `V` of `Over U` to functions
`I → Γ(X, V.left)`. Its forward map applies the actual local coordinate
morphisms, and its inverse sums scalar multiples of the actual basis sections.
The expansion lemma proves the left inverse, and the Kronecker pairing proves
the right inverse. `localSectionBasis` is the basis obtained from that equivalence.
Its vectors are exactly those sections and its representation map is exactly the
coordinate morphism. Both basis vectors and coordinates commute with restrictions
to smaller opens.

`localSectionEndomorphism` evaluates a genuine endomorphism of `M.over U` on the
sections of `V.left`, as a ring homomorphism into the linear endomorphism ring.
Naturality intertwines this action with restrictions. The final theorem proves
that each matrix entry in the constructed section bases restricts along the
actual structure-sheaf ring map.

All scheme, ring, module and basis-index objects have the same universe level,
as in the imported sheaf constructions. No reducedness, nonemptiness, affineness
or nonzero coefficient-ring assumption is imposed. The empty finite basis and
empty open are permitted. These constructions are derived from the published
coordinate and expansion identities and the pinned Mathlib basis-from-functions
construction. Worker 57 authored this extension. It does not assert a Hodge
comparison, arithmetic integrality or the existence of a representing PEL scheme.
