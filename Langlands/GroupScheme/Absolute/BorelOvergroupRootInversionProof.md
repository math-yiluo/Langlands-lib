# Proof of `Langlands.GroupScheme.AbsoluteBorelOvergroupRootInversionStatement`

This module proves the published proposition `Langlands.GroupScheme.AbsoluteBorelOvergroupRootInversionStatement` (module `Langlands.GroupScheme.Absolute.BorelOvergroupRootInversion`) at every universe `u`. The statement says that for `G` connected reductive over an algebraically closed field, a split maximal torus `j`, a smooth connected closed overgroup `i : P ⟶ G` of `j`, and a root `α` such that `α` and `−α` both lie in the weight support of `P`, some relative Weyl element sends `α` to `−α` and preserves that weight support.

The theorem is `Langlands.GroupScheme.absoluteBorelOvergroupRootInversion : AbsoluteBorelOvergroupRootInversionStatement.{u}`, with no hypotheses.

## Proof

A short tactic proof: introduce the hypotheses of the statement and apply the published theorem `AbsoluteBorelOvergroup.exists_supportPreserving_weylInverter_of_both_signs`, which has exactly these hypotheses and this conclusion.

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.AbsoluteBorelOvergroup.exists_supportPreserving_weylInverter_of_both_signs` (module `Langlands.GroupScheme.Absolute.BorelOvergroupRootInversion`)
