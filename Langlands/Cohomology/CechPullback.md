# Ordered Čech cochains on preimage covers

Internal derivation from the published ordered Čech cochain and degree-one quotient APIs.
For a continuous map `f : X ⟶ Y`, an abelian presheaf `P` on `X`, and any family of opens
`U` on `Y`, `cochains` identifies the ordered cochains of the pushforward of `P` on `U`
with the cochains of `P` on the preimage family. It restricts along the equality of the
finite intersections. Both transports commute with the differential. `cocyclesEquiv`
restricts this equivalence to one-cocycles, and `h1Equiv` descends it through the ranges
of the zero-cochain differentials. No cover, finiteness of the family, or sheaf condition
is needed. The spaces and coefficients have universe `u`, and the index type has an
independent universe `w`. This identifies fixed-cover Čech quotients, without asserting
compatibility with the actual Ext-defined sheaf cohomology comparison.
