# Comparisons for affine scheme topology assignments

This is derived infrastructure for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Proposition 2.1 and its proof,
printed pages 2–3. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The rings and schemes have the common universe `u`. The spectrum point
equivalence commutes with actual relative spectrum morphisms because taking
the ring map of a composite reverses composition.

The two bundled homeomorphisms express the induced topologies in the existing
family transports. They require no axioms on the assignments and no topology
on the value ring.

Functoriality makes restriction along an algebra isomorphism a homeomorphism
for an arbitrary algebra assignment: restriction along the inverse is its
continuous inverse. The direct spectrum comparison is the global-section
comparison followed by restriction along the inverse of the actual
Gamma-Spec algebra isomorphism. Consequently a functorial algebra assignment
is recovered by transporting to schemes and back. The inverse comparison uses
the homeomorphism built from the specified spectrum equivalence, so its inverse
is the specified inverse point map.

The products of the direct spectrum point homeomorphisms identify the scheme
and algebra compatible-pair subspaces. The global-section point
homeomorphisms do the same for the algebra-to-scheme transport. Naturality
proves the compatibility iff in both cases, and the subtype topology is
the induced topology of the product of the assigned factor topologies.

Functoriality on actual scheme morphisms makes postcomposition with an actual
relative isomorphism a homeomorphism: postcomposition with its inverse is the
continuous inverse. The canonical affine isomorphism followed by the direct
spectrum point equivalence is the global-section point equivalence.
Consequently a functorial scheme assignment is recovered by transporting to
algebras and back. Both recovery statements use functoriality; neither asserts
that arbitrary assignments are invariant under isomorphism.

The evaluation algebra assignment transports to the evaluation scheme assignment
by the definition of the global-section topology. In the reverse direction the
direct spectrum point homeomorphism identifies the induced topology with the
evaluation topology on algebra maps. These two evaluation identities need only
a topology on the value ring.
