# Simplicity and original stable subgroups

Worker 133. This module proves the first simplicity clause of Renard I.3.2.
The source is the registered 9 July 2026 French edition
`renard-2026-representations-groupes-reductifs-padiques`, I.3.2,
printed p.21 / PDF p.27, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 133 read the surrounding printed pp.19–22.

The internal helper lemmas express categorical simplicity as the usual
dichotomy for stable additive subgroups with the original action. For a
simple object, each subgroup inclusion is zero or an isomorphism. Conversely,
the dichotomy makes every nonzero monomorphism surjective and hence an
isomorphism in the published abelian category. Nontriviality rules out a
zero isomorphism. The concrete mono and epi criteria and the subgroup
objects are published inputs.

For a corner submodule `P` of the fixed part, `fromFixed` is the additive
closure of the values `a • z`, with `z` in `P`. Associativity proves its
stability under the original action. Applying `e` to any such generator
amounts to applying the corner element `eae` to `z`; additive closure
therefore projects into `P`. Simplicity of the ambient module now makes
`fromFixed P` zero or the whole module. In the first case `P` is zero
because its elements are fixed by `e`; in the second it contains every
fixed vector. The assumed nonzero fixed part supplies nontriviality.

This is the source's generation argument, expressed using stable additive
subgroups rather than a cyclic-module notation. Ring and module universes
remain independent.
