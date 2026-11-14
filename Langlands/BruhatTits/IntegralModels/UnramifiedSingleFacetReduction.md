# Upstairs radical generation reduced to a singleton

This is an internal reduction of the published
`UnramifiedUpstairsRadicalRootGenerationStatement`, at arbitrary universe `u`.
It proves no new singleton radical formula. The only new proposition definition,
`UnramifiedUpstairsSingletonRadicalRootGenerationStatement`, restricts the
published formula to apartment singletons while preserving the order of the
common subgroup, apartment points, smooth models, and represented radicals.

The implemented reduction uses only published building comparisons.
`sharpFixer_eq_singleton_of_subset_facet` writes a sharp fixer as the supremum
of the actual root fixers and applies the general-field AS4 root-fixer
constancy theorem to a nonempty facet subset and to its chosen singleton.
The field is arbitrary here; in particular this step does not impose local
compactness on the maximal unramified extension.

`unramifiedZeroFixer_eq_singleton_of_subset_facet` first applies the bounded
zero/sharp comparison just to the chosen singleton. Its normalizer input is
the published `MaximalUnramified.simplyConnectedNormalizerAffineWeyl`.
The singleton zero fixer is the join of the zero fixer of the entire
apartment and the singleton sharp fixer. Constancy of the latter, its
containment in the zero subgroup, and its pointwise fixation of the original
subset give the inclusion back into the subset zero fixer. The opposite
inclusion follows from antitonicity of pointwise fixers. No facet or subset
is asserted to be bounded.

Finally, `unramifiedUpstairsRadicalRootGeneration_of_singleton` chooses a
point in the nonempty subset, reuses the same characterized smooth model
using the zero-fixer equality, and rewrites every positive root fixer using
`rootFixerPlus_eq_of_nonempty_subset_facet`. It leaves the reduction map,
generic integral-point map, and represented unipotent radical unchanged.
The common subgroup is chosen before the subset, as in the original target.

The mathematical provenance is the facet reduction explained in the
published target's Markdown, derived there from Kaletha–Prasad (2023),
Definitions 6.1.2 and 7.4.1, Lemmas 6.3.20–6.3.21, and Proposition 7.6.4(1).
This file supplies an internal Lean route through the existing Library
normalizer comparison rather than a separate direct formalization of those
source items.
