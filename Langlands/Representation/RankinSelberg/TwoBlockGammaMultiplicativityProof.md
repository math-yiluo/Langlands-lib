# Two-block gamma multiplicativity in every rank order

`Langlands.RankinSelberg.twoBlockGammaMultiplicativity` proves exactly the
published `TwoBlockGammaMultiplicativityStatement.{uF,uV,uW}`. For every
canonical p-adic field, supplied nontrivial unitary additive character and
supplied self-dual Haar measure, it constructs certified rational gamma
factors for both block pairs and certifies their product for the actual
`F.canonicalNormalizedProductInduced (succBlockShape m h) sigma`.
The field, test carrier and dependent block carriers have independent
universes. All positive ranks in both orders and arbitrary full
Whittaker-type representations, including reducible representations, are
retained.

The proof closes the seven premises of
`twoBlockGammaMultiplicativity_of_inputs_commonUniverse` with these published
theorems:

| Conditional input | Closed theorem |
| --- | --- |
| Full type of normalized product induction | `normalizedProductWhittakerType` |
| Certified gamma construction input | `whittakerTypeGammaConstructionInput` |
| Equal-rank pair exchange | `equalRankFactorSwap` |
| Dominant-rank gamma base, including equality | `twoBlockGammaDominantRank` |
| Adjacent-rank gamma base with first upper block of rank one | `twoBlockGammaAdjacentRank` |
| Rank-one test gamma base | `twoBlockGammaRankOne` |
| Scalar rank-one full type | `rankOneWhittakerType` |

Each theorem is imported from its proof module. In particular, the three
analytic inputs are their gamma conclusions, with complete symmetric
certificates. The conditional proposition definitions and the companion
L-factor conclusions are not used as proofs of these inputs.

The imported descent packages actual full Whittaker-type representations
in the common carrier universe `U = max uF uV uW`, which is closed under
normalized induction. The construction theorem supplies chosen certified
gamma units. Symmetry uses the larger-rank-first certificate convention in
unequal rank and the closed exchange theorem at equality. The trivial
scalar character, lifted through its actual linear representation
equivalence, supplies a full-type rank-one auxiliary object.

The first downward induction fixes the second block and handles a first
upper block of rank one. The dominant base covers larger test ranks, the
adjacent base starts the remaining descent, and enlargement of the test
representation by the auxiliary object supplies the next rank. Comparing
the enlarged product with its opposite pair factorizations and the
rank-one test identity permits cancellation of certified units. The second
downward induction fixes both blocks, starts at the dominant base and
uses the first induction for its opposite factorizations. This proves
every rank order without an irreducibility or rank hypothesis.
`TwoBlockGammaDescent.certified` then transports the internally assembled
two-element family to the original dependent family through the actual
normalized induced-representation equivalence, retaining both block
certificates and the full induced certificate.

The final Lean term instantiates the common-universe theorem with
`u := max uV uW`. It applies
`twoBlockGammaMultiplicativity_of_commonUniverse` to recover the original
independent universes. That transport lifts the test representation and
every carrier of the entire ordered block family, preserves full type,
and uses `normalizedProductInducedUniverseLiftEquiv` for the actual induced
representation. Complete symmetric gamma certificates transport back
through these equivalences. The supplied field, character, measure,
ordered sizes and rational factors remain fixed.

This is an internal assembly of published results implementing the two
descents of Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg
Convolutions* (1983), Section 7.1–7.2, printed pages 438–442, for Theorem
3.1(i), printed pages 404–405. The registered original is
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original sections 3–7 and registered errata were checked; no applicable
registered erratum was found.

The analytic base proofs own the source's lower-to-upper normalization
comparison. They reverse the complete ordered family, apply actual
normalized induction conjugation and transport complete factor
certificates to the upper convention. For example, the dominant proof
discharges `LowerGammaDominantInput` and applies
`gammaDominant_of_lower`, whose `lowerReversedToUpperEquiv` reverses sizes,
dependent carriers and actions together. The descent consumes these
proved upper-convention conclusions and assumes no induction equivalence.
It uses neither a finite-block multiplicativity theorem nor a later
result depending on this theorem. The original target pair and its
imports are unchanged.
