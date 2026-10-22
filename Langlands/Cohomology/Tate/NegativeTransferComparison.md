# Tate restriction and ordinary homological transfer

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

The target `restriction_groupHomology` identifies the constructed Tate
restriction in every degree `-(n+1)`, for `n > 0`, with ordinary homological
transfer through Mathlib's existing Tate-to-group-homology isomorphisms.
The ordinary transfer is constructed independently on the homogeneous
standard resolution, with a proved augmentation-preserving comparison and
explicit coset formulas. It is not defined by conjugating Tate restriction.

The proof compares two chain-induced maps into the auxiliary zero-splice
complex. At degree minus one both send a norm-zero representative to the
ordinary zero-chain class of its inverse-coset sum. The comparison propagates
downward using the coinduced augmentation sequence. The restricted coinduced
middle term has vanishing negative auxiliary homology, so the actual
connecting morphism is injective. The already proved connecting compatibility
of Tate restriction and the new chain comparison then gives the induction
step. Finally the existing negative-degree isomorphisms identify the auxiliary
maps with ordinary homology maps.

The universal theorem quantifies over the original finite group, every subgroup,
and every coefficient representation in arbitrary universe `u`. It adds no
acyclicity, comparison, or desired-operation hypothesis. The vanishing used in
the proof is established from the actual restricted coinduced representation.

This formal proof route is internal dimension shifting for the classical
restriction/transfer convention in Serre, *Local Fields*, Greenberg translation,
GTM 67 (1979), Chapter VII section 7, printed pages 118–119 (PDF pages 124–125),
and Chapter VIII sections 1–2, printed pages 127–130 (PDF pages 133–136).
Registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
