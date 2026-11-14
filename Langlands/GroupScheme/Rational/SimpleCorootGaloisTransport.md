# Actual Galois transport of simple coroots and their points

This internal helper works over arbitrary fields `k` and `K` with an algebra
structure and an affine group scheme over `k`. It retains the supplied
`GaloisCompatiblePinningData`: an actual split pinning after base change, a
specified descended commutative torus and inclusion, a torus identification,
and the ordinary Galois action on the actual simple roots. Neither finiteness
nor Galoisness of the field extension is required for this helper.

`action_coroot` proves that the same permutation transports the actual simple
coroots. The proof transports the pinned root datum through the specified torus
identification. The transported inclusion is closed and the torus is split;
the published finite-Weyl-image theorem therefore applies, with finite type
provided by the pinned connected reductive group. Ordinary Galois transport
preserves its actual-root-datum predicate. The given root equality and published
coroot uniqueness then identify the coroots. Small private lemmas retain the
closedness, monicity and finite-image data explicitly.

`torusPointEquiv` is the actual multiplicative point equivalence of the specified
torus identification. `torusCorootPoint` evaluates the actual pinned simple
coroot and transports its value through that equivalence.
`torusCorootPoint_rationalConjugate` proves that coefficient conjugation carries
this point to the permuted coroot evaluated at the conjugated field unit. Its
proof uses the published rational cocharacter evaluation transport and the
preceding coroot equality.

`torusCoordinates` transports the preceding module's simple-coroot coordinate
equivalence to the base change of the descended torus. This definition retains
the explicit hypothesis that the integral coroot span is the entire cocharacter
lattice. No coordinate covariance, orbit decomposition or rational root-generation
claim is made in this helper. Empty simple-root support is allowed.

The provenance is internal composition of the published torus transport,
ordinary Galois root-datum transport, finite-Weyl-image coroot comparison,
rational cocharacter evaluation and actual simple-coroot coordinate APIs.
