# Support obstructions for two adjacent cuspidal twists

Author: Worker 168.

This internal helper defines `Langlands.Classification.RepeatedCuspidalSupport.pairSupport`
and proves multiset obstructions for the actual positive-rank cuspidal data of a
supplied p-adic field and its supplied topological data. The field and
representation-carrier universes remain independent. It does not assert a
Jacquet transfer, compute derivatives, or establish rank-three irreducibility.

For a cuspidal datum `ρ`, `pairSupport T ρ a b` is the multiset consisting of
`a` copies of the actual determinant twist `νρ = ρ.twist 1` and `b` copies of
`ρ`. The twist uses the existing residue-normalized determinant norm.

The published theorem `cuspidalIntegralTwistFreeness` at the integers 1 and 2
proves that `νρ ≠ ρ` and `ν²ρ ≠ ρ`. Applying its first consequence to `νρ`
also proves `ν²ρ ≠ νρ`. Thus if the image of a multiset `s` under the positive
twist is bounded by `pairSupport T ρ a b`, then `νρ` cannot occur in `s`:
its image would be neither endpoint of the pair. This is the theorem
`upper_not_mem_of_shift_le`; it places no other restriction on `s`.

If in addition `s` itself is bounded by that pair support, deleting all upper
copies from the upper bound shows that `s` consists of at most `b` copies of
`ρ`. Write it as `replicate k ρ`. Its shifted image is `replicate k (νρ)`;
counting the upper endpoint in the shifted-support inequality gives `k ≤ a`.
The theorem `le_lower_min_of_support_and_shift_le` therefore proves
`s ≤ replicate (min a b) ρ`.

The two corollaries `upper_repeat_support_eq` and `lower_repeat_support_eq`
specialize this bound to `{νρ,νρ,ρ}` and `{νρ,ρ,ρ}`. In either case the
only possible `s` satisfying both inequalities is the empty multiset or the
singleton `{ρ}`. These are conditional multiset conclusions; constructing
support inequalities for actual representations remains a separate obligation.

The provenance is internal: the argument combines the existing twist identities
and the published integral twist freeness proof with elementary multiset
membership, deletion, replication and counting. No external assertion is cited.
The sole project import is `CuspidalIntegralTwistFreenessProof`, whose proof
uses admissible Schur central characters and scalar uniformizer evaluation.
Its lower import closure contains no segment-constituent existence theorem,
multisegment classification, ordered quotient coverage, tempered uniqueness,
square-integrable classification or regular exhaustion. The other direct
import is Mathlib's elementary `Data.Multiset.Filter`. The implemented proof
uses no global support decomposition or classification conclusion.
