# A single surviving graded quotient

Author: Worker 508.

This internal algebra construction evaluates an actual finite functor
filtration at an input, without changing its subrepresentations or its
successive quotients. If every quotient vanishes at that input, the ambient
carrier is a subsingleton. If all quotients except one specified occurrence
vanish, it constructs an actual categorical isomorphism from the ambient
representation to that quotient. The specified quotient may itself be zero.
The coefficient ring, monoid, carrier and input category universes are
independent. No field, finite length, splitting or nonvanishing assumption is
used.

The proof uses the published deletion theorem
`ObjectRepFiltration.zeroFactorDeletionTheorem`: select exactly the distinguished
index, delete every other zero quotient, and identify the resulting length
with one by an explicit equivalence of finite index types. The published
`RepFunctorFiltration.lengthOneGradedIso` identifies the ambient representation
with the shortened filtration's sole actual quotient. The deletion theorem's
representation equivalence then identifies it with the specified original
quotient. Thus the result retains an occurrence, even when distinct original
quotients happen to be equal. It does not assert a natural isomorphism on all
inputs from an objectwise vanishing hypothesis.

The all-zero conclusion uses the independently proved
`objectRepFiltrationSubsingleton`. This construction is elementary finite
filtration algebra, derived from those published results; it introduces no
additional literature assertion and uses no classification conclusion.
