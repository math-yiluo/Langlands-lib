# Full reductive Isom schemes from three explicit geometric inputs

This is an internal assembly from the actual fpqc generic-isomorphism cover,
coproduct gluing of local isomorphisms, and the full single-cover Isom scheme
descent construction, using the action transport of `OuterIsomorphismTransport`.
It cites no new literature theorem.

`reductiveIsomorphismSchemeOfSingleIsomorphism` assumes the full
`ReductiveAutomorphismSchemeGeometryStatement`, a supplied relative adjoint
quotient of `G`, and an actual isomorphism of `G,H` after a single étale
surjective base change. Apply the Aut geometry input over the new base.
Postcomposing its universal automorphism family with the supplied isomorphism
gives a full local Isom representative on the same smooth parameter.
Its supplied outer quotient is transported on the same class parameter and
class map. The published equality between the pulled-back original inner
action and the quotient's local inner action identifies the source actions.
The original full-centre quotient action is faithful on every refinement.
The single-cover descent constructor therefore supplies an actual full Isom
scheme over the original base.

`genericIsomorphismSchemeOfGeometry` retains the original arbitrary-universe
domain-DVR inputs and specified fraction field. It takes three explicit
proposition inputs:

- `ReductiveAutomorphismSchemeGeometryStatement`;
- `RelativeAdjointQuotientExistenceStatement`;
- `ReductiveFpqcLocalIsomorphismStatement`.

The second supplies a relatively affine full-centre quotient of the original
source group, whose reductivity follows from the published quotient
reductivity theorem. The actual generic-isomorphism cover supplies an fpqc
local isomorphism; the third input gives an actual étale covering family.
The local actual isomorphisms glue over its scheme coproduct without a
finiteness restriction. That coproduct maps étale surjectively to the original
base, so the preceding single-cover construction applies.

The output is a `GroupIsomorphismScheme G H`, containing the actual universal
natural `LocalGroupIso` and bijective classification on every relative scheme
test. The final theorem derives
`GenericIsomorphismSchemeExistenceStatement` from those same three inputs.
It does not assume that the representing scheme extends the specified
generic isomorphism as a distinguished integral point.

All three geometric statements remain explicit hypotheses and are not proved
by this module. The Library proves them, and `genericIsomorphismSchemeExistence`
(`Reductive/GenericIsomorphismSchemeExistenceProof`) applies the final theorem
of this module to those proofs.
