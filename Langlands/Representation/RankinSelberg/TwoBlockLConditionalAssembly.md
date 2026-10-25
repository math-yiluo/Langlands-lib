# Conditional two-block L-polynomial rank descent

This module is internal support for the two-block proof of JPSS (1983),
Theorem (3.1)(ii), with its two descending inductions from Section 7. It proves
an implication from explicit analytic and representation-theoretic inputs to
`TwoBlockLFactorMultiplicativityStatement` in a stable carrier universe. It
does not prove the closed multiplicativity statement of the parent task.

The namespace is `Langlands.RankinSelberg.TwoBlockLConditionalAssembly`.
`PolynomialLDivides P A` means
`∃ Q : ℂ[X], ∃ e : ℕ, X^e * A = Q * P`.
This is exactly the relation permitted by the published target. Ordinary
polynomial divisibility implies it at exponent zero. The implemented proofs
establish transitivity and compatibility with the product of two factors.
Consequently, ordinary reverse comparison `P | Paux`, an auxiliary cleared
relation, and two forward block cleared relations give the desired original
cleared relation. There is no removal of the powers of `X`, coefficient
normalization argument, or Laurent-ideal extraction premise.

The certificate-swap helper follows the definition of the symmetric
L-polynomial relation at unequal ranks and uses the explicit
`EqualRankFactorSwapStatement` premise at equal ranks. The certificate
uniqueness helper transfers a two-block conclusion to independently chosen
certified polynomials for the same actual representations.

The actual auxiliary upper induction has successor-rank family `![0, r]`,
ordered factors `(χ, π)`, and total successor-rank parameter `1 + r`. Thus its
ambient rank is definitionally `1 + (r + 1)`. The native shape is proved equal
to `Shahidi.twoBlocks 1 (r + 1)`, and the native dependent family is proved
heterogeneously equal to `Shahidi.pairFamily`. A Sigma bundle of positive rank
functions and dependent representations yields an exact equivalence of the
L-polynomial certificates for their canonical normalized inductions. This is
an identification of actual ordered inductions, rather than an inference
from the commutativity of a polynomial product.

Full Whittaker type of the auxiliary induction is obtained conditionally from
`NormalizedProductWhittakerTypeStatement`. The concrete descent combines the
reverse total comparison, the auxiliary two-block conclusion, the two forward
auxiliary block conclusions, and block cross certificates equal to `1`.
Certificate uniqueness identifies independently chosen auxiliary polynomials.
The full-type and equal-rank swap inputs remain explicit throughout.

The added character is the exact scalar action conjugated through
`ULift.moduleEquiv.symm` to `ULift ℂ`, as in the published restricted rank-one
extension interface. Its actual representation equivalence is constructed.
The character selector assumes the published full Whittaker-type
high-ramification and scalar rank-one type propositions, scalar equal-rank
swap, and actual unbounded conductors of continuous quasicharacters. It takes
the maximum of two block conductor bounds, twists the trivial character, and
transports the resulting certificates to the lifted action. Only the two
block cross factors are used. No vanishing assertion against the total
original induced representation is required.

The restricted reverse adapter applies the unchanged
`RankOneExtensionLDivisibilityStatement` with the original total representation
as test, the original test representation as the smaller base, and the exact
lifted character. It transports the standard pair-family certificate and
swaps certificates into the concrete descent orientation. Its rank margin is
precisely `r + 3 ≤ t + 1` in successor-rank parameters.

The first actual downward induction fixes the original two-block family and
assumes `m 0 = 0`. Its original first GL(1) block remains an arbitrary
Whittaker-type representation on its arbitrary carrier; no character
classification is used. The induction measure is `t - r`, with dominant and
adjacent cases supplied by their explicit base propositions. In the remaining
range the auxiliary test parameter is `1 + r`, decreasing the measure. The
forward block comparisons use respectively the rank-one-test base and the
dominant base. The restricted reverse adapter supplies the total comparison.

The second induction also uses `t - r`, now for arbitrary original blocks.
Dominant pairs are the base. Each forward block comparison invokes the first
induction on the auxiliary family, whose first upper block has rank one. For
`r + 3 ≤ t + 1` the reverse comparison uses the restricted lemma. At
`t = r + 1`, it instead assumes `EqualRankReverseAt F ψ ν`, the internal
fieldwise predicate defined in this module. This predicate requires, for each
base rank `r + 1`, arbitrary full-type test rank `r + 2`, and arbitrary
continuous `χ`, certified polynomials for the test against the base and the
actual upper induction `(χ, base)`, with `Pbase | Pind`. It asserts neither its
own proof nor the availability of a closed endpoint theorem. The separate
endpoint statement/proof task remains necessary.

The exported theorem
`twoBlockLMultiplicativity_of_inputs_commonUniverse` concludes exactly
`TwoBlockLFactorMultiplicativityStatement.{uF, max uF u, max uF u}`. Its
premises are the three L base propositions, restricted reverse divisibility,
the fieldwise equal-rank reverse input for every field/character/measure,
symmetric L-polynomial existence, stable-universe equal-rank swap, normalized
product full type, scalar-versus-block high-ramification vanishing, scalar
rank-one full type, scalar-versus-block equal-rank swap, and unbounded
continuous quasicharacter conductors for every field. None of these analytic
premises is discharged by this contribution. The independent original
carrier universes also require the separately owned common-universe
transport before the parent task's closed target can be proved.

Provenance is internal: the relation algebra, certificate packaging, exact
auxiliary family identification, and conditional assembly are derived from
the existing Library definitions and implemented elementary proofs. The
induction route is motivated by H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, Theorem (3.1)(ii), printed pages 404–405, and Section 7,
printed pages 438–443. The source lower induction reverses whole blocks and
tensor factors when transported to the upper convention; these analytic
comparisons are retained in the separately supplied exact upper-convention
premises here. Printed Lemma (5.5), pages 423–427, only supplies the strict
rank margin. Section 7.2, equation (7.2.13), printed page 443, reaches the equal
rank boundary outside that margin. This module makes no claim that the
restricted lemma proves that endpoint or that a published erratum resolves
it. The later Section 9.3 tail theorem and full finite-block multiplicativity
are not used.
