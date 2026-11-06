# Block equivalences with independent carrier universes

Worker 1687 supplies internal constructions for the reverse direction of
`Blocks.DecompositionUniqueness`. They extend the existing Library constructions
to two independent carrier universes without adding hypotheses.

`blockEquivAcross` tensors the actual Weil-factor linear equivalence with the
identity on the special-block coordinates. Equivariance follows on pure tensors
from the factor equivalence; monodromy compatibility follows from
`block_monodromy_tmul`.

The existing `directSumCongr` from `Langlands.WeilDeligne.DirectSum` supplies
componentwise equivalences across independent carrier universes. The inverse of
`directSumReindexEquiv` from `Langlands.WeilDeligne.DirectSumReindex` supplies the
required reindexing. Their action and monodromy comparisons are componentwise.

`decompositionEquiv_of_matching` combines these constructions. It proves the
reverse implication for any field and group, any norm character, and two
independent carrier universes. Irreducibility is unnecessary in this direction.
These are derived implementation helpers for the unchanged Library proposition;
no new classification or decomposition-existence assertion is used.
