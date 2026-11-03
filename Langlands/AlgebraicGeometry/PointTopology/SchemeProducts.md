# Products of actual scheme point spaces

Author: Worker 105.

This is a derived construction from the published
`schemePullbackPointHomeomorph`, specializing the fibre-product clause of
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), Proposition 3.1, printed page 4. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The arbitrary-scheme, relative formulation is the documented generalization
already supplied by that published pullback homeomorphism.

The commutative rings `R` and `S` lie in a common arbitrary universe, and
`S` is an `R`-algebra. Only `S` is topologized. It satisfies
`IsTopologicalRing S`, `IsLocalRing S` and `IsOpenUnits S`. The schemes
`X` and `Y` over `Spec R` are arbitrary. No finite-type, affineness,
separation, Hausdorffness or compactness hypothesis is used.

`schemeProductPointHomeomorph R S X Y` identifies actual relative
`S`-points of the categorical product `X ⊗ Y` in `Over (Spec R)` with the
product of the actual relative point sets of `X` and `Y`. All three point
sets carry their independently defined `schemePointTopology`, and the pair
space carries the ordinary product topology.

The construction views the chosen categorical product as a pullback over
the terminal relative scheme, whose structure map is the identity of
`Spec R`. It applies the existing arbitrary-scheme pullback homeomorphism.
Two relative points have equal composites to this terminal object by its
universal property, so the compatibility subtype is homeomorphic to the
whole pair space by forgetting the tautological proof. Composing these
homeomorphisms gives the definition.

The forward-map law `schemeProductPointHomeomorph_apply` identifies the
map with `p ↦ (p ≫ fst X Y, p ≫ snd X Y)`. The inverse-map law
`schemeProductPointHomeomorph_symm_apply` identifies it with the actual
categorical pairing `(p,q) ↦ lift p q`, using the two projection identities
and injectivity of the constructed homeomorphism. The direct corollary
`continuous_schemePointPair` exposes continuity of this inverse pairing.
These are intrinsic laws of the constructed homeomorphism.

This generic product comparison supplies point-topology infrastructure.
Identifying a particular group multiplication, Levi decomposition or open
cell map with its underlying scheme morphism, and providing that morphism's
algebraic isomorphism or open-immersion property, remain separate obligations.
It asserts no measure-theoretic property or whole-paper completion.
