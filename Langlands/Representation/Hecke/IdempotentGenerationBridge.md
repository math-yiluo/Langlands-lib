# Generation by compact-open fixed vectors and the Hecke idempotent

This internal bridge compares Renard's two generation criteria. It works for a
Hausdorff locally compact nonarchimedean group, a left Haar measure, any compact
open subgroup, and smooth complex representations in an independent carrier
universe. It imposes no reductive-group or Iwahori hypothesis.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`. The relevant passages
are I.3.2 (printed pages 19–22), III.1.4–III.1.5 (printed page 60), and VI.10.6
Proposition (ii) (printed page 214). The bridge is an internal consequence of the
published integrated action and local-unit results, rather than a separately
numbered assertion in the book.

`compactOpenIdempotent` packages the normalized indicator and its published
idempotence proof. `fixedVectorGeneratedProperty` is the usual criterion that
every subrepresentation containing the compact-open fixed space is the whole
representation.

The implemented proof constructs both directions of the submodule comparison.
An additive Hecke submodule is closed under complex scalars: for each vector a
local idempotent fixes it, and multiplying that idempotent by a complex scalar
realizes the desired scalar action. Left translating the same idempotent
realizes the group action, so the submodule is a subrepresentation. Conversely,
the canonical inclusion of an actual smooth subrepresentation intertwines the
integrated Hecke actions, proving stability under every Hecke element.

The published normalized-indicator projection lemmas identify the original
idempotent-fixed additive subgroup with the compact-open fixed vector space.
Applying the least-submodule characterization of
`IsGeneratedByIdempotent` then proves
`fixedVectorGenerated_iff_idempotentGenerated`. No subquotient closure or
categorical equivalence of fixed-vector functors is asserted here.

`fixedVectorGeneratedProperty K` abbreviates the existing `Langlands.Jacquet.fixedVectorGenerated K.toSubgroup`.
