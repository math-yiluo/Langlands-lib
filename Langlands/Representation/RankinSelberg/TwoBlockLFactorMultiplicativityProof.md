# Two-block L-polynomial multiplicativity in every rank order

Author: Worker 465.

`Langlands.RankinSelberg.twoBlockLFactorMultiplicativity` proves exactly the
published `TwoBlockLFactorMultiplicativityStatement.{uF,uV,uW}` from
[TwoBlockMultiplicativityStatement](TwoBlockMultiplicativityStatement.md).
The theorem has no additional premises. It retains independent field, test
carrier and dependent block carrier universes, every canonical p-adic field,
the supplied nontrivial unitary additive character and self-dual Haar measure,
all positive ranks in both orders, and arbitrary full Whittaker-type inputs,
including reducible representations.

For the actual ordered upper induction
`F.canonicalNormalizedProductInduced (succBlockShape m h) σ`, the conclusion
constructs a polynomial `P` with its complete symmetric L-polynomial
certificate, a family `Pi` with complete certificates for both original block
pairs, and ordinary polynomials `Q` and an exponent `e : ℕ` such that

```text
X ^ e * ∏ i, Pi i = Q * P.
```

Factor existence and full Whittaker type of the induced representation are
provided by imported proofs within the assembly.

The implemented proof applies
`TwoBlockLVerifiedInputAssembly.twoBlockLFactorMultiplicativity_of_remainingInputs`
and discharges each of its five explicit hypotheses by a closed Library
theorem:

| Analytic input | Closed theorem |
| --- | --- |
| Dominant rank, including equality | `twoBlockLDominantRank` |
| Adjacent rank with first block of rank one | `twoBlockLAdjacentRank` |
| Test rank one | `twoBlockLRankOne` |
| Restricted reverse rank-one extension comparison | `rankOneExtensionLDivisibility` |
| Full Whittaker-type high-ramification vanishing | `whittakerTypeHighlyRamifiedLVanishing` |

The first four inputs use both carrier universes `max uF uV uW`.
High-ramification vanishing uses first carrier universe zero for the scalar
character and second carrier universe `max uF uV uW`. The verified-input
assembly internally supplies its other seven inputs by the closed theorems
`equalRankRankOneExtensionLDivisibility`, `symmetricLPolynomialExists`,
`equalRankFactorSwap` at both required carrier specializations,
`normalizedProductWhittakerType`, `rankOneWhittakerType`, and
`padicQuasicharacterUnboundedConductor`. Its endpoint adapter identifies the
exact lifted scalar character used in the descent. Thus every conditional
interface used here has a proof.

The imported
[conditional assembly](TwoBlockLConditionalAssembly.md) executes two downward
inductions on `t - r`. The first treats a first block of rank one, retaining
an arbitrary full Whittaker-type representation on that block; its bases
are dominant rank and adjacent rank. The second treats arbitrary two-block
families, using the first induction for the two forward block comparisons.
The auxiliary ordered upper induction is `(χ, π)`. A character with conductor
above both block bounds makes its two cross factors equal to `1`. Reverse
divisibility, the auxiliary forward comparison and the two block comparisons
then compose to the displayed cleared polynomial equation.

The restricted reverse theorem is applied only within its strict rank
margin. At the adjacent-total boundary `t = r + 1`, the separate closed
equal-rank reverse theorem supplies the comparison. Powers of `X` are
retained throughout. Common symmetric-factor existence supplies certificates
with their compatible-measure quantifiers, and uniqueness identifies the
independently chosen certified polynomials.

The analytic bases concern the actual normalized induction. Their
lower-to-upper transport reverses the entire ordered family of sizes,
dependent carriers and representations through the normalized opposite-product
representation equivalence, then transports the complete certificates and
reindexes the block product. The descent likewise identifies its actual
auxiliary ordered family. These representation identifications are part of
the imported proofs. Finally,
`twoBlockLFactorMultiplicativity_of_commonUniverse`, used inside the
verified-input assembly, lifts the original carriers through representation
equivalences and transports all certificates back, preserving `Q`, `e` and
the equation. This gives the original independent universes.

Provenance is internal composition of the named Library results and the
implemented Section 7 descent. The original source is Jacquet,
Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions* (1983), registered
as `jpss-1983-rankin-selberg`, Theorem (3.1)(ii), printed pages 404–405;
Sections 3–7, especially Lemma (5.5), pages 423–427, and Section 7,
pages 438–443. The retained source has SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original and registered errata were checked during development; no
applicable registered erratum was found. The companion assembly documentation
explains the separate equal-rank endpoint.

The proof follows the dependency order from the restricted comparison through
Section 7. It imports no unrestricted or finite-block L-multiplicativity
proof and no Section 9.3 tail theorem. The target pair and all its imports are
unchanged.
