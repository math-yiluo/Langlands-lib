# Pinned rigidity from split-pinned opposite-factor pairs

Worker 1368 implements this internal composition of the conditional pinned
rigidity reduction with the published maximal-torus self-centralization proof.
Workers 1416 and 1467 contributed the underlying reduction plan, and Worker 1467
implemented the equivariant root-coordinate helper bundled with that reduction.

`SplitPinnedOppositeFactorPairsStatement.{u}` is the proposition that every actual
split pinning of every affine group scheme over every field in universe `u`
has `RelativeRoot.HasOppositeFactorPairs` for its actual torus inclusion. This
is a geometric existence assertion: for each actual nonidentity rational root
point quantified by that predicate, two actual opposite-root factors exist
whose product with the point normalizes the torus. It is restricted to supplied
split pinnings and does not assert general relative-root factorization.
This module does not prove that proposition.

`SplitPinning.automorphism_eq_refl_of_pairExistence` applies the existing
`automorphism_eq_refl_of_oppositeFactorPairs` to the supplied pinning. Its
torus self-centralization premise is supplied by `maximalTorusCentralizer`,
using the connected reductivity and maximality fields of that same pinning.
The only extra premise beyond the original automorphism and its two fixedness
hypotheses is actual opposite-factor-pair existence for this pinning.

`pinnedAutomorphismRigidity_of_splitPinnedOppositeFactorPairs` proves the exact
published `PinnedAutomorphismRigidityStatement.{u}` from the single proposition
`SplitPinnedOppositeFactorPairsStatement.{u}`. Its proof supplies
`maximalTorusCentralizer` and the retained pair-existence premise to
`pinnedAutomorphismRigidity_of_prerequisites`. The imported reduction derives
whole simple-root subgroup fixedness on all test schemes from the actual
pinning differential hypothesis, propagates it using actual pairs and root
reflections, and concludes by closed torus-and-root generation.

The provenance is internal composition of the imported proofs. The published
`Absolute.MaximalTorusCentralizerProof` supplies self-centralization over every
field and on every test scheme, without an additional premise. Its paired
Markdown describes its structural assembly and Milne source. No new external
assertion is used here. The target and its imported Lean/Markdown pairs remain
unchanged; arbitrary universes, all field characteristics, central tori and an
empty root system remain in scope. Opposite-factor-pair existence remains an
unproved prerequisite, so this is a conditional intermediate contribution,
not an unconditional proof of the task target.
