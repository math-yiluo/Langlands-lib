# Actual segment head from a signed Jacquet class

This internal assembly constructs an actual equivalence to a supplied special
head from an explicit signed Jacquet class identity. Its input is a segment
subrepresentation `πZ`, a supplied strong special head `πS`, and an actual
irreducible `τ`. It also takes an integer `ε` equal to `1` or `-1` and the
canonical exact-class equality
`[r_B τ] = ε • [reversedJacquetObject B πZ]`, where `B` is the full uniform
cuspidal block shape. It proves `ε = 1` and chooses an actual representation
equivalence from `τ` to `πS`. The result neither constructs `τ` nor supplies
the signed class identity; the unconditional segment exchange remains open.

The implemented proof first pulls the centrally separated simple series of
the actual Jacquet module of `πZ` back along block reversal. The simple
factors and their distinct scalar values are preserved, and the central
element is pulled back by the inverse group equivalence. The actual
uniform reversed Jacquet object is identified with this pullback.

The actual embedding of `πZ` into the increasing segment induction is nonzero
because `πZ` is irreducible. First adjointness gives a nonzero map from its
Jacquet module to the increasing tensor. The actual reversal transport and
tensor reindexing give a nonzero map from the reversed Jacquet object to the
decreasing tensor, which is irreducible. The signed central-class transfer
therefore forces `ε = 1` and constructs a surjective map from `r_B τ` to that
decreasing tensor. Its target is nonzero, so this map is nonzero. First
adjointness then embeds the irreducible `τ` into the decreasing induction.
The supplied special head is its strong socle, so strong socle uniqueness
identifies `τ` with `πS`.

The imported `SegmentJacquetSubobject` constructs the actual separated series
using associated Jacquet filtration, exactness and subobject multiplicities;
it does not identify the entire Jacquet module with one tensor.
`QuasicuspidalJacquetExchange` supplies the actual reversal object and the
reversal of the nonzero tensor map; this assembly does not use its Aubert
class identity. `CentralSignedClassTransfer` uses positive natural
composition multiplicities to exclude the negative relative sign and actual
central polynomial projections to transfer the simple quotient across exact
class equality. `SegmentHeadDecreasingSocle` identifies a supplied special
head with the decreasing strong socle using the independently proved
special-constituent existence and uniqueness. These are lower algebraic and
actual representation inputs, without the excluded analytic classification
or multisegment exhaustion. No additional original-literature theorem is
transcribed here.

The final head construction retains independent field and carrier universes,
arbitrary primes, supplied fields and topologies, and the saturated segment
carrier universe of the final exchange target. It uses the existing actual
exact finite-length Grothendieck groups, retaining nonsplit exact relations.
