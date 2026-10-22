# Proof of the p-adic cuspidality comparisons

This pair proves the exact closed proposition
`Langlands.CuspidalSupport.PadicCuspidalityComparisonTheorems` in
`CuspidalityComparisonStatement`. The field and representation-carrier
universes are independent. All primes, actual p-adic fields, compatible
topological realizations, positive ranks, and complex representations
from that statement are retained. No irreducibility or finite-dimensionality
assumption is added. The statement pair and all imported pairs are unchanged.

## Single-block comparison

`singleBlockCuspidalityClause` installs the supplied field topology and
its certified local-field structures. It uses the published standard-radical
criterion `GeneralLinear.isSupercuspidal_iff_standard` to reduce
supercuspidality to admissibility and vanishing of all proper standard
unipotent coinvariants. The Levi predicate already splits as admissibility
and vanishing for every proper standard refinement.

For admissibility, `B.singleBlockLeviEquivContinuous hB F.Carrier` is a
topological group equivalence whose forward homomorphism is the actual
`B.leviEmbedding F.Carrier`. The generic theorem
`isAdmissible_comp_continuousMulEquiv_iff` therefore identifies the
admissibility of the exact pullback in the statement with that of the
ambient representation.

For a refinement `S`, `Jacquet.coinvariantsMapEquiv` identifies the
pullback's coinvariants at `refinedUnipotent F.Carrier B S` with ambient
coinvariants at its image under the actual embedding. The geometry lemma
`singleBlock_refinedUnipotent_map` identifies that image with the standard
unipotent subgroup of `B.singleBlockRefinementEquiv hB S`. The induced
bijection preserves `Subsingleton` of these quotient carriers.

The refinement equivalence is surjective onto all ambient block shapes.
Given an ambient shape in the forward implication, the proof chooses its
preimage refinement. The reverse implication uses the shape associated to
the given refinement. In both directions
`singleBlock_refinedParabolic_ne_top_iff` transports the actual subgroup
properness condition. Thus the quantifiers range over exactly the required
proper parabolics; no choice of an additional geometry hypothesis is needed.

## Closed aggregate and provenance

`padicCuspidalityComparisonTheorems` combines the imported
`standardJacquetSupercuspidalityClause` with this single-block clause.
The former uses conjugation transport of coinvariants and the equivalence
between parabolic Jacquet quotients and ambient radical coinvariants.
The implementation of the latter is explained above. The final example
checks the complete closed telescope with independent universes.

These are derived interface comparisons, as explained in the unchanged
statement Markdown. Their underlying convention is Bernstein–Zelevinsky
(1977), sections 2.1–2.4, printed page 446 (PDF page 7), with transport in
section 1.7, printed page 443 (PDF page 4), registered as
`bernstein-zelevinsky-1977-induced-i`. The present proof composes actual
Library group, quotient and admissibility constructions; it does not claim
a separately numbered theorem from that source.
