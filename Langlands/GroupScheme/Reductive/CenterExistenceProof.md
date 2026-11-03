# Existence of the full scheme-theoretic centre

Author: Worker 1360.

`Langlands.GroupScheme.schemeTheoreticCenterExistence` proves the exact published
proposition `Langlands.GroupScheme.SchemeTheoreticCenterExistenceStatement.{u}`.
It applies to every field in the arbitrary universe `u` and every actual group
scheme `G` with `IsConnectedReductive G`. It constructs an actual group scheme
`Z` and homomorphism `z : Z ⟶ G` with `IsSchemeTheoreticCenter z`.

The implemented proof uses the published theorem
`fieldFixedSubgroupRepresentability` for the automorphic action
`AutomorphicAction.conjugation (𝟙 G)` of `G` on itself. The acting group's
affineness is supplied by `IsConnectedReductive.isAffineHom`. That theorem
provides a representing group scheme, its inclusion, equality of its range
with the fixed subgroup functor, and closedness of the inclusion.

The helper `conjugation_id_fixedSubgroup_eq_center` identifies that fixed
subgroup functor with the existing `center G`. Both conditions quantify every
test scheme and every further test morphism. On each such test, the published
formula `conjugation_act` turns fixedness into `h * g * h⁻¹ = g`, equivalent to
`g * h = h * g`. The proof checks both implications with the group laws.
Composing this functor equality with the representative's range equality gives
the range condition in `IsSchemeTheoreticCenter`; its other condition is the
closedness already supplied by the representability theorem.

This is an internal derivation from published Library results. The original
centre assertions and their errata checks are documented in
`Reductive/CenterStructureStatement.md`; the general fixed-subgroup theorem's
source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Proposition A.8.10(1), as documented in `FixedRepresentabilityStatement.md`.
The proof uses the Library's closed-factorization-locus construction through
`FieldFixedSubgroupRepresentabilityProof`, without introducing a new external
mathematical assertion.

Only affineness from the reductivity premise is used. The construction does not
require a chosen centre or assume its representability. Closedness and
representation of the full all-test functor are conclusions. There is no
perfectness, characteristic, splitness, smoothness, or reducedness assumption on
the centre; finite nonreduced centres are retained.
