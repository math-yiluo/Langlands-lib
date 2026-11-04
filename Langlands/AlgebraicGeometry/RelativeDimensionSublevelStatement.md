# General relative-dimension sublevel statements

Worker 105 states the two general assertions about the actual source sets
`relativeDimensionSublevel f n` from Stacks Section 29.29, tag 02FW.
The retained original HTML belongs to the registered source
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA-256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`.
The dimension is the minimum-neighbourhood dimension of the actual point
in the residue-field scheme fibre, as in the source.

`RelativeDimensionSublevelOpenness` states Lemma 29.29.4: every natural
sublevel is open when the morphism is locally of finite type.
`RelativeDimensionSublevelRetrocompactness` states Lemma 29.29.6: the same
sets are retrocompact when the morphism is locally of finite presentation.
Retrocompactness means that intersection with any compact open of the
source is compact, using Mathlib's `IsRetrocompact`. The conjunction
`RelativeDimensionSublevelProperties` is the exact proof target.
These are proposition definitions, not proofs. They retain arbitrary
schemes and all natural bounds, with no affine, separated, quasi-compact,
surjective or Noetherian hypothesis added. Local finite type in the
openness clause is not replaced by local finite presentation.

The following lemmas are derived comparisons, proved in this module.
Local dimension at an actual point is nonnegative: a minimizing open
neighbourhood contains that point, whose closure gives an irreducible
closed subset and hence a chain of length zero. This holds for arbitrary
topological spaces and therefore for the actual relative fibre dimension.

The exceptional set where relative dimension differs from zero is the
complement of the zero sublevel. At a positive natural value `n + 1`,
the exceptional set is the union of the `n` sublevel and the complement
of the `n + 1` sublevel. These comparisons use nonnegativity and the
discrete finite values in `WithBot ℕ∞`. They also cover infinite local
dimension, without a separate finite-dimensionality assumption.
Closure of constructible sets under Boolean operations therefore makes
each exceptional source set constructible whenever the actual sublevels
are constructible.

For a locally finitely presented, quasi-compact morphism with qcqs target,
Mathlib's proved Chevalley theorem sends that exceptional constructible
source set to a constructible set. The existing actual fibre comparison
identifies its complement with `pureDimensionFiberLocus d f`. Empty fibres
belong to this pure-dimension locus vacuously, in agreement with the
componentwise convention. This proves the conditional constructibility
reduction and its corollary from `RelativeDimensionSublevelProperties`.
The source sublevels become constructible by openness and retrocompactness.
The reduction requires no quasi-separatedness premise on the morphism
in addition to the explicit hypotheses.

This unit supplies an exact general-dimension proof target and proves how
it would provide the dimension part of the constructibility prerequisite
for Conrad Theorem 3.4(2). It does not prove the two general sublevel
assertions, geometric-connectedness locus constructibility, or Conrad's
filtered descent conclusion.
