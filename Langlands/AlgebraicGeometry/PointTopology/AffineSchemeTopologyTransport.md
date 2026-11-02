# Transport of the four affine topology axioms

This is derived proof infrastructure for Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Proposition 2.1, printed
pages 2–3. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For a scheme topology assignment satisfying its corresponding axiom, the
direct spectrum point homeomorphisms transport functoriality to restriction
of algebra maps. A surjective algebra map has a closed immersion as its
spectrum morphism, so the same commuting square transports the embedding
axiom. Evaluation on the polynomial coordinate transports line normalization.

For any colimit pushout cocone of finite-type algebras, the actual relative
spectrum cone is limiting. Its compatible-pair subspace is homeomorphic to
the algebra compatible-pair subspace by the product of the direct spectrum
point homeomorphisms. Naturality identifies the composite map with the
specified algebra pushout comparison. Thus the actual-scheme pullback axiom
implies the algebra pushout axiom for the transported assignment.

In the reverse direction the actual global-section pullbacks and the
global-section point homeomorphisms transport functoriality. For an actual
closed immersion with affine target, the pullback on global sections is
surjective, so the algebra quotient embedding axiom gives the scheme
embedding. Functoriality ensures that the transported algebra assignment has
the required direct spectrum comparison; this comparison transports line
normalization.

For an arbitrary limiting relative affine scheme cone, the actual
global-section cocone is colimiting. The factorwise global-section
homeomorphisms identify the two compatible-pair subspaces. The proved
coordinate comparison square identifies the resulting composite with the
specified scheme pullback comparison. Together these arguments transport all
four axioms in both directions. The two recovery identities from the comparison
module then prove `AffineSchemeTopologyTransportProperty`.

All rings and schemes have a common universe. No separation, finite
presentation or topology on the coefficient ring is used.
