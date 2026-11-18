# Quasi-split inner forms of reductive group schemes over any base

`Langlands.GroupScheme.relativeQuasiSplitInnerFormExistence` proves the unchanged
`RelativeQuasiSplitInnerFormExistenceStatement.{u}` in every universe, with no
additional hypotheses.

For every scheme `S`, reductive group scheme `G` over `S`, supplied fppf quotient
`p : G ⟶ Gad` by the full centre, and supplied action `c` restricting along `p`
to conjugation, the theorem supplies an actual group scheme `G'` with:

- a surjective étale cover and a natural local group isomorphism from `G` to
  `G'` whose discrepancy is inner for the supplied action `c`;
- `IsRelativeQuasiSplit G'`;
- a relative Borel subgroup of `G'` containing a closed fibrewise maximal
  relative torus.

The implemented proof applies
`relativeQuasiSplitInnerFormExistence_of_pinnedComparison` to the unconditional
`relativePinnedComparisonExistence`. The first theorem constructs the corrected
affine pinned atlas, descends its group scheme by arbitrary-base étale
effectivity, identifies it locally with the original group with inner
discrepancy, and supplies the Borel and torus on that same descended group.
The second theorem supplies the natural pinned comparison required by this
construction, including its pullback coherence, torus and cocharacter
preservation, and discrepancy sections in every supplied full-centre quotient.

This file is an internal composition of those Library proofs. The final theorem
has exactly the imported statement as its type; pinned comparison existence is
discharged by the imported theorem. The base scheme may be empty, disconnected,
nonaffine, or non-Noetherian, and no constancy of root datum is assumed. The
statement pair and its imported definitions are unchanged.
