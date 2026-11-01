# Rank-one test reduction support

This is internal derived support for the rank-one analytic base. It uses the
current Library definitions and proved transport results, rather than asserting
a new numbered result of the literature.

A continuous complex scalar character of a supplied p-adic realization has open
kernel. The implementation first applies the published continuous-character
open-kernel theorem to its determinant pullback on GL(1), whose actual topology
is nonarchimedean. Pulling that open kernel back along the continuous scalar
embedding gives the original kernel because the determinant of a scalar matrix
in rank one is the scalar itself. `quasicharacterSmoothCharacter` retains the
same monoid homomorphism and supplies this kernel witness to smooth induction.
The full Whittaker-type twist comparison then uses the determinant kernel and
its trivial restriction to the upper unipotent subgroup. Admissibility, finite
generation over the group algebra, and the entire functional-space condition
are all retained.

The L-certificate transport applies the published `isPairLPolynomial_twist`
separately for every compatible quotient measure and leaves its measure
existence witness unchanged. The symmetric relation uses the same theorem in
each rank branch, replacing the twisting character by its inverse when the
larger-rank-first definition exchanges the representations. Equal ranks retain
their original order.

For a rank-one scalar test, twisting by the inverse character cancels its action.
This specializes the full L transport with the test first. The corresponding
gamma theorem uses the published `rankOneGammaTwist`. For positive other rank,
the symmetric definitions place that representation first on both sides. At
rank one, the implementation uses the published fixed-character equal-rank
gamma exchange in both directions. Its full Whittaker-type inputs are supplied
by the scalar character theorem and the full twist comparison. Thus the gamma
helper asks for full type only in that equal-rank case.

These helpers transport supplied full certificates. They do not establish
analytic existence, convergence, induced Whittaker type, gamma multiplicativity,
or L divisibility.

The final two conditional theorems make the remaining analytic input precise.
`twoBlockGammaRankOne_of_trivial_test` takes a universally quantified two-block
gamma theorem for `rankOneCharacter 1`, with arbitrary full Whittaker-type block
representations, canonical p-adic fields, nontrivial unitary additive characters,
and supplied self-dual Haar measures. Its conclusion is the existing
`TwoBlockGammaRankOneStatement`. The corresponding
`twoBlockLRankOne_of_trivial_test` takes the analogous trivial-test L theorem and
concludes the existing `TwoBlockLRankOneStatement`. Each analytic premise retains
the independent field and block-carrier universes. Each conclusion additionally
retains the independently quantified universe of the original test carrier.

For either proof, `r = 0` permits application of the published
`rankOneCharacterReduction` to the original full-type test representation. This
produces a continuous quasicharacter and an actual representation equivalence to
its scalar action. Twist every block by that quasicharacter composed with its
own determinant. The full-type twist theorem above verifies every hypothesis of
the supplied trivial-test base. Apply the base to this entire ordered family.

The induced representation comparison uses the actual
`normalizedProductDeterminantTwistEquiv`, supplied with the smooth scalar
character constructed above. Its source is the determinant twist of the
original normalized upper block induction; its target is normalized upper block
induction of the twisted family. In particular, no induced equivalence or induced
Whittaker type is added as a premise. The gamma proof uses positivity of both
block ranks and their rank sum to prove that the induced rank exceeds one, so
the induced gamma twist comparison requires no equal-rank full-type hypothesis.
Individual blocks of rank one use their supplied full type in the equal-rank
exchange.

The full certificate equivalence theorems transport the induced certificate back
along this actual induction equivalence. The scalar-test twist helpers then
recover certificates for the quasicharacter test and the original blocks and
induction. Finally, the actual rank-one test equivalence transports each
certificate to the original test carrier. The gamma factors and their product
are unchanged. The L proof retains the same `P`, family `Pi`, and witnesses `Q`
and `e`; its final equality is exactly
`X ^ e * ∏ i, Pi i = Q * P`, in the original direction.

These are conditional reductions, not proofs of the two closed analytic bases:
the universal trivial-test analytic premises remain to be established. This
module does not use unrestricted multiplicativity or any Section 7 descendant.
It does not supply the source lower-to-upper ordered reversal or the Section 5
analytic argument. Its provenance is the internal composition of the named
Library constructions, full-type transport, and full certificate equivalences.
