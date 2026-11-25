# Actual identity coherence of the Nilp quotient-square comparison

This module identifies the actual quotient-square comparison at a Nilp
identity with reduction of the actual identity-base comparison.

`baseAlongSquare_identity_unit` uses the two proved whole coefficient-unit
isomorphism equalities. After eliminating the equality of the final supplied
coefficient map with the identity, the forced equality comparison is the
actual identity. The proof passes to the actual integral full-order Hom maps, retains both
identity corrections explicitly and uses composition associativity and the
actual inverse equation to cancel the right identity-base correction.

`reductionIdentityScalarIso` is exactly the actual scalar correction forced
by preservation of identity by the quotient functor, regarded through the
structural scalar algebra map. `reductionBaseChange_identity_unit` specializes
the coefficient-unit equation to the actual Nilp quotient map and canonical
quotient naturality equation. It retains this correction explicitly, then
composes with the reduced action's actual identity-base map. The resulting
whole integral atlas isomorphism is reduction of the original identity-base
isomorphism. No detection by point evaluations is used.

`reductionIdentityUnitTestSquare` restricts the same two whole integral routes
to a specified quotient test chart and rationalizes their equality with
actual identity isomorphisms on the other two edges. All formal inverse maps
are retained.

The coefficient/acting rings, Nilp objects and rational field have the indicated
separate universes. The finite coordinate type is arbitrary. Rationalization
uses the existing domain/fraction-field hypotheses, and the given quotient
chart is invertible on its test. Covers may be infinite. Original framed
identity/composition comparisons are constructed in
`DrinfeldFramedIdentityComparison` and `DrinfeldFramedCompositionComparison`;
class functor laws and representability remain separate.
