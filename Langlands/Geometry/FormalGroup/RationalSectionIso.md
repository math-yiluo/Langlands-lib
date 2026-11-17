# Invertible rational sections and the global tensor comparison

`RationalSectionIso F M N U` consists of an actual section of the rational
Hom sheaf and an actual section in the reverse direction whose two
composites are the actual identity sections. O is commutative, R is an
O-algebra and F is an O-algebra field. R and F share a universe; O may
have a different universe. All coordinate types are finite and may differ.
This is an internal construction from the already proved section calculus.

Identity, inverse and composition use the actual section operations.
Associativity and the two identity laws prove that composition retains a
two-sided inverse. The implemented inverse-uniqueness argument inserts
the forward map followed by its inverse, reassociates and cancels. Thus
equality is detected by the forward section. This proves the composition,
identity and inverse laws for these objects.

Restriction applies the genuine sheaf restriction to both sections.
Naturality of composition and identity gives the two inverse equations.
Equality on the forward section proves the restriction identity and
composition laws and compatibility with identity, inverse and composition
of invertible sections.

`ofIso` sends both actual integral maps of an integral isomorphism into
the rational sheaves on each open. Agreement on integral images proves
its inverse equations and restriction compatibility.

For the existing global tensor `QuasiIsogeny`, O is additionally a domain
and F is its fraction field. `ofQuasiIsogeny` applies the actual linear
`ofGlobalOn` map to both tensors. Its preservation of composition and
identities proves the two inverse equations. The resulting comparison
commutes with restriction and preserves identity, inverse and composition.
It agrees with `ofIso` on quasi-isogenies from integral isomorphisms.

This construction requires no representing moduli object or universal
formal module. It does not claim injectivity, surjectivity or equivalence
of the global-tensor comparison. In particular it does not identify these
invertible sections with `LocalQuasiIsogeny`, which is defined by local
scalar multiples of actual integral isogenies. That comparison and its
required finite-kernel and inverse constructions remain unproved.
