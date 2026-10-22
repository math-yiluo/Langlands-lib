# Quasinet topology arguments

Author: Worker 36.

These auxiliary lemmas support the exact Library target
`Langlands.Analytic.AtlasTopology.QuasinetTopologyStatement`.

The implemented argument follows Berkovich 1993, section 1.1, Lemma
1.1.1 and the local compactness remark immediately after that lemma,
printed pages 13–14 (PDF pages 10–11). The exact retained source and
fingerprint are recorded in `Definitions.md`.

At a point, the quasinet supplies finitely many members which contain
the point and whose union is a neighborhood. The neighborhood filter
within a finite union is the supremum of the neighborhood filters
within its members. Continuity on every member therefore gives
continuity within that union, and hence continuity at the point.
Mathlib's `Topology.IsCoherentWith` then supplies the equivalent
relative-openness and relative-closedness tests.

The product of two quasinets is proved to be a quasinet by multiplying
the finite witness families. Their union is exactly the product of the
two neighborhood unions. To prove the Hausdorff criterion, the relative
diagonal in a product of members is the image of their compact
intersection in the product of their Hausdorff subspaces. It is closed
there. The product-quasinet closedness test makes the whole diagonal
closed, which is equivalent to ambient Hausdorffness. In the reverse
direction, intersections of two compact subsets of a Hausdorff space
are compact.

The family covers the space because each neighborhood union contains
its point. Enlarging the family preserves the same finite witnesses.
The whole-space singleton family is proved to be a net, providing the
topological single-chart example without assuming an analytic structure.
When all members are compact, their finite union is a compact
neighborhood. This proves weak local compactness without separation
assumptions; with Hausdorffness, Mathlib upgrades it to local
compactness.

These are intrinsic topology proofs. They do not assert the missing
analytic-domain factorization theorem or construct an affinoid atlas.
