# Fixed block polynomials for the actual adjacent-rank real ray

This internal module proves `adjacentLowerPair_fixedRealRayCertificates` for
an actual pair of representations of `GL_(r+1)`, with full standard Whittaker
type, any quasicharacter, and the supplied self-dual additive Haar measure.
The field, first representation carrier and test representation carrier retain
their independent universes. The additive character is the existing continuous,
nontrivial unitary additive character. No irreducibility premise is used.

`AdjacentLowerPairFixedRealRayCertificates` records two fixed complete symmetric
L-polynomial certificates and one real threshold. For every real parameter above
that threshold it supplies a complete certificate for the actual second-block
deformed lower induction, together with the exact relation
`X^e * (P0 * P1.comp (C (spectralPoint q u) * X)) = Q * P`.
The auxiliary polynomial and exponent may depend on the parameter. The complete
certificates retain the compatible-quotient existence witness and the universal
quantification over compatible quotient measures; none is replaced by a bare
normalization or a rational-function equality.

The ordered lower predecessor sizes are `[r,0]`. `adjacentLowerPairBlocks` uses
the original first representation and `rankOneExtensionCharacter` on the
universe-preserving lift of complex scalars. `adjacentLowerPair_sum` proves the
rank sum. `oppositeInducedEquiv_of_sizes` transports the lower induction when
the ordered sizes and block actions agree. Its proof substitutes those
equalities, after which the induction equivalence is reflexive; no reversal or
permutation is introduced in this comparison.

`rankOneExtensionCharacter_realTwisted` identifies the literal determinant
complex-power twist with `AdjacentCompactMatrix.realTwistedCharacter`. After
extensionality its proof is the commutativity of the two complex scalar factors.
`adjacentLowerPair_realTwistEquiv` applies the size transport to the actual
large-twist model. On the first block the determinant-power parameter is zero,
so the action is unchanged. On the second block it uses the proved scalar
identity. This gives an equivalence of the actual induced representations,
including their section carriers.

The main proof chooses complete fixed block certificates using the published
`symmetricLPolynomialExists`. It then applies
`adjacentRankLargeTwistLDivisibility`, which already supplies actual complete
induced and block certificates and exact polynomial divisibility on one real
ray. Uniqueness identifies its first block polynomial with the fixed first
polynomial. `symmetricLPolynomial_determinantComplexPower` supplies the complete
rescaled fixed second certificate, and the scalar identity and uniqueness
identify the varying second polynomial with that rescaling. Symmetry and
`IsPadicSymmetricLPolynomial.congr_equiv` transfer the induced certificate to
the actual second-block deformation. Substitution proves the displayed exact
polynomial relation.

This is derived internal composition of the named Library interfaces, rather
than a new assertion attributed directly to the literature. The unchanged
`AdjacentRankCertifiedRealRay` and `AdjacentRankRealRayClearing` dependencies
are included while their publication is pending; Worker 1191 is credited for
the reused real-ray bridge dependency. This module discharges the fixed
certificate existence condition for the specified lower family. Formal clearing
and specialization to zero are consumers of this result. Neither exact
adjacent-rank parent gamma/L proposition is proved in this module.
