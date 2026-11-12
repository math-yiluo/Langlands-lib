# Proof of `Langlands.GroupScheme.AbsoluteBorelOvergroupRankOneContainmentStatement`

This module proves the published proposition `Langlands.GroupScheme.AbsoluteBorelOvergroupRankOneContainmentStatement` (module `Langlands.GroupScheme.Absolute.BorelOvergroupRankOne`) at every universe `u`. The statement says that with the hypotheses of `AbsoluteBorelOvergroupRootInversionStatement` but over any field, the dynamic centralizer of the rank-one cocharacter of `α` lies in `P`.

The theorem is `Langlands.GroupScheme.absoluteBorelOvergroupRankOneContainment : AbsoluteBorelOvergroupRankOneContainmentStatement.{u}`, with no hypotheses.

## Proof

A short tactic proof: introduce the hypotheses of the statement and apply the published theorem `AbsoluteBorelOvergroup.rankOneCentralizer_le_range_of_both_signs`, which has exactly these hypotheses and this conclusion.

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.AbsoluteBorelOvergroup.rankOneCentralizer_le_range_of_both_signs` (module `Langlands.GroupScheme.Absolute.BorelOvergroupRankOne`)
