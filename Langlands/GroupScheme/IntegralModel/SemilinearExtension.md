# Integral isomorphisms from stable section transport

This internal construction consumes an explicit fixed-ring smooth
homomorphism extension property. It neither asserts nor proves that property
for any particular ring. All coefficients have arbitrary common universe `u`.

`HasSmoothHomExtension` states the extension property for actual integral
models over a fixed domain R with fraction field L: a homomorphism of generic
groups carrying the integral points of a smooth source into those of a target
extends to a compatible integral model homomorphism.

For two smooth models Q and P, a generic isomorphism from Q to P, and exact
section transport from P to Q, stability under inverse generic-point actions
supplies both integral-point inclusions. Surjectivity of section transport is
needed for the forward inclusion. The reverse inclusion follows from an exact
right-inverse point action and injectivity of the generic isomorphism. The
construction applies the supplied extension property in both directions and
uses the published generic-rigidity construction `Iso.ofHoms` for the inverse
laws.

`galoisTwistIso` applies this construction to the actual coefficient twist of a
smooth model of a group pulled back from a smaller field. The integral base
map is assumed invertible and compatible with the specified field
automorphism. The exact section transport is the proved
`twist_integralPointMap_galois`; its generic-point actions are the existing
`rationalConjugate` for the automorphism and its inverse. Stability under both
is assumed. The resulting actual integral-model isomorphism extends the
canonical generic descent isomorphism. Its named generic comparison has
exactly the same forward morphism and point map as the existing
`descentBaseChangeIso`. The explicit `galoisTwistIso_generic_comm` law is the
canonical generic semilinear law consumed by the descent solution comparison.
The reverse integral-point inclusion is also provided separately and needs
only stability under the inverse action, without surjectivity of integral
section pullback.

The auxiliary `retarget` changes only the chosen generic-fibre identification
along a specified isomorphism. It preserves smoothness and maps exactly the
integral-point image along that isomorphism; integral-section preimages and a
forward inclusion therefore identify that image with another model's image.
The auxiliary `isoOfIntegralPointsEq` applies the same supplied extension
property to both identity generic morphisms between smooth models whose
integral-point images are equal.

This is a conditional construction internal to the descent development, based
on the published actual twist, point transport and generic rigidity APIs. It
constructs no effective descent and does not prove the extension criterion or
KP Fact 2.10.16.
