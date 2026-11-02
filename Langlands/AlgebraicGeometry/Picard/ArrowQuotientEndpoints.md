# Endpoints of the canonical sheaf of Picard arrow classes

This internal construction continues the actual endpoint-kernel construction
in `SmoothArrowRelation`. It descends the endpoint pair to the fixed canonical
etale sheaf of arrow classes and proves that the descended map is a
monomorphism. The geometric quotient theorem is a separate obligation.

`atlasEndpointIso` represents the full endpoint-pair presheaf by the actual
product of the object atlas with itself in `Over S`. Its maps send a map to
its two projections and reconstruct a map by the product universal property.
Subcanonicity of the etale topology therefore proves
`atlasEndpointPresheaf_isSheaf`.

Given a scheme representing all actual arrows and a full represented endpoint
kernel square, the square's commutativity makes the endpoint map constant on
the kernel relation. `arrowKernelQuotientEndpoint` applies the published
`quotientSheafDesc` construction. Its compatibility equation is the equality
of whole natural transformations on the complete arrow presheaf.

The proof of `arrowKernelQuotientPresheafEndpoint_mono` uses representatives
only in the pointwise quotient presheaf, where every class has one. Equality
of endpoint images supplies an actual kernel section by the evaluated
pullback's existence property, which proves equality of the quotient classes.
Monomorphisms in the presheaf category are detected componentwise.
For `arrowKernelQuotientEndpoint_mono`, left exact sheafification preserves
this monomorphism, and the endpoint target is already an etale sheaf. The
resulting sheafified map followed by the inverse sheafification unit is the
descended endpoint map. This proves injectivity for all sheaf sections without
assuming that they admit global arrow representatives.

`arrowKernelQuotientFst` and `arrowKernelQuotientSnd` are its two components.
Their composites with the canonical quotient map recover the two original
endpoint transformations. All schemes, tests, morphisms and sheaf sections
are retained, uniformly in the universe. No algebraic-space representability,
smoothness of these descended projections, equivalence-relation structure on
the object atlas, or identification with the ordinary Picard class sheaf
is asserted here.
