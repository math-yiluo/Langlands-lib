# Topological comparison for actual filtered scheme points

This proof implements the derived target
`FilteredRingPointTopologicalComparison` from
`FilteredRingPointTopologicalStatement`. The theorem
`filteredRingPointTopologicalComparison` has exactly the type
`FilteredRingPointTopologicalComparison.{u}`: it covers every commutative
ring, small filtered category, diagram of commutative algebras, cocone with
an actual `IsColimit` witness, locally finitely presented scheme and family
of stage topologies in one arbitrary universe `u`, and adds no hypothesis.
Its source motivation is Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (31 December 2011), printed pp. 5–6, Theorem 3.4(1) and
Remark 3.5, and printed p. 9, section 4. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The target's Markdown explains the derived generality and the remaining
arithmetic and model obligations.

`filteredRingPointTopologicalComparison` first applies the published
`filteredRingPointComparison` to the actual algebra-colimit cocone and the
locally finitely presented scheme. This supplies stage representatives of
every cocone point and the bijectivity of the canonical comparison, so no
bijectivity premise is needed. The bijection upgrades to
`ringPointColimitHomeomorph` for the independently defined final topologies.
The underlying function is definitionally the canonical point comparison
`ringPointColimitMap`. Under continuous open transitions, composing this
homeomorphism with the open stage maps supplied by the published
`filteredRingPointOpenStages` proves that every actual cocone-point stage
map is open.

For local compactness, the point-factorization result chooses a stage
representative. Continuity of the stage map pulls back an arbitrary
neighborhood, local compactness at that stage supplies a compact
neighborhood inside its preimage, and the stage map takes it to a compact
neighborhood inside the original neighborhood. Openness ensures that the
image is a neighborhood. This argument requires no injectivity or
Hausdorffness.

For second countability, the proof forms the disjoint union of the stages
indexed by the selected countable subtype. This sum is second countable.
Its actual map to cocone points is continuous and open by the stage
properties and surjective by the stated coverage premise, so it is an open
quotient map, and `Topology.IsOpenQuotientMap.secondCountableTopology` supplies
second countability of the target. No injectivity is used.

Under injective transitions, the open stage embeddings of
`filteredRingPointOpenStages` compose with the homeomorphism. For
Hausdorffness, represent two distinct target points at stages i and j, then
move both representatives to the filtered common stage
`IsFiltered.max i j`. The transition identity `ringPointColimitι_changeRing`
in the actual point colimit proves that their target images are unchanged,
so their representatives at the common stage are distinct. Disjoint open
neighborhoods there map to disjoint open neighborhoods in the target by its
open embedding (`separated_by_isOpenEmbedding`).

This proves the complete named generic target. It supplies no arithmetic
specialization, varying-model descent, model independence, fiber-product
comparison, or whole-paper completion.
