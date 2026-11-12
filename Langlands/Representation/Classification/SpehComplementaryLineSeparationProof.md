# Proof of complementary irreducibility from integral-line support

Author: Worker 1530, Task 5495.

The theorem proves the exact proposition
`IntegralLineComplementaryIrreducibilityReduction.{uF,uV} F T`.
Its premise is `UnlinkedSocleProductIrreducibility`; the supplied actual support
already implies irreducibility of `S`.

For each of the two actual determinant twists, the proof uses the published
`multisegmentSocleExhaustion` to obtain a socle multisegment. The theorem
`isSupercuspidalSupport_of_isZelevinskySocle` identifies its cuspidal content as
an actual support of the same representation. The original support, transported
by `IsSupercuspidalSupport.twist`, is another such support. The published
`glSupercuspidalSupportUniqueness` identifies these full multisets, retaining
multiplicities.

Every segment base occurs in its segment's content and therefore in the
multisegment content. Hence each base in the first factor is `ν^(m+α) ρ` for an
integer `m`, and each base in the second is `ν^(l-α) ρ` for an integer `l`.
The paired helper module `SpehComplementarySegments` proves that a nonzero
`α` strictly between `-1/2` and `1/2` has nonintegral `2α`. It also derives from
published linkage orientation and real cuspidal-twist injectivity that segments
whose base exponents differ nonintegrally cannot be linked. These facts exclude
all links across the two factors, in either order.

Applying the retained unlinked-socle product theorem to the actual two-block
induction gives a strong Zelevinsky socle relation for the whole product. Its
irreducibility clause is the desired conclusion, since that product is
definitionally the statement's `twistedProductInduced`.

Provenance: an internal composition of the named published support and socle
results and the paired elementary separation lemmas. The proof keeps field and
representation universes independent. It does not use unitarizability of `S`
or of either twist, and the general unlinked-product result remains an explicit
premise of the proved reduction. The final Speh application is a separate unit.
