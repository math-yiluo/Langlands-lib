# Proof of the full number-field adelic level colimits

Authors: Worker 208 (proof and draft exposition), Worker 695 (scope clarification and verification).

`numberFieldAdeleLevelColimit` proves the exact proposition
`NumberFieldAdeleLevelColimitStatement` in an arbitrary universe `u`.

The proof reuses `SubringCover.desc` from the finite-sector colimit proof.
That construction extends a compatible family of ring maps on a monotone
subring cover by choosing a containing level for each element. Comparing
choices in a union level proves independence, and placing pairs of
elements in a union level proves the ring laws.

For an arbitrary cocone in `CommRingCat`, apply the construction to the
actual full number-field adelic levels. Naturality of the cocone legs is
exactly the needed compatibility, and the full-level exhaustion theorem
supplies the cover. The extension's evaluation formula proves the
factorization equations. Evaluating any adele in one containing level
proves uniqueness, giving the ring categorical colimit structure.

For a cocone in `TopCommRingCat`, forget topology and construct the same
ring map into its actual vertex. On each level it agrees with the
original continuous leg. The full number-field final-topology theorem
makes the extension continuous. The same equations and exhaustion prove
factorization and uniqueness in topological commutative rings.

Every ring and topology in this argument is the existing actual one,
including all archimedean coordinates. This proves the derived
number-field universal properties described in the statement Markdown.
The argument permits `S = ∅` and never assumes a nonempty finite-place
indexing type. All infinite coordinates remain unrestricted at every
level, including the empty finite level; the finite-set unions and cover
construction also apply when the finite-place type is empty.

This focused proof discharges only the named ring-level target of parent
`886bf565-95e9-4dc6-8a9d-73284a523668`. The parent retains all five sections,
actual global fields of both characteristics, nonaffine and algebraic-space
point comparisons, model descent, change of models and every remaining
assertion. The provenance of this derived categorical statement and its
relationship to Conrad's ring direct-limit description are recorded in
`NumberFieldAdeleLevelColimitStatement.md`.
