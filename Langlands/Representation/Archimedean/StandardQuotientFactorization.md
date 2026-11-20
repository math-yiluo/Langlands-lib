# Realizing a standard quotient through a factored reverse intertwiner

`IsGKSubquotientMap` expresses that a linear map from a specified stable subspace
is surjective and intertwines the restricted compact-group and complex Lie algebra
actions. It uses `IsGKSubmodule` for the stability witnesses that define the two
restricted actions. This internal predicate allows both the real and complex
standard-module comparisons to return the same form of quotient witness.

The two lemmas realize the irreducible quotient of an ordered standard module on a stable
subspace of an intermediate standard module. They keep the supplied quotient `p` and give a
surjective map from `LinearMap.range A` to its carrier, where `A` is the supplied intertwiner
to the intermediate module. The new map composes with the range restriction of `A` to give
`p`. The complex lemma uses `complexReverseIntertwinerKernelReduction` with
`complexTemperedStandardIrreducible`. The real lemma takes
`RealReverseIntertwinerKernelStatement` as a premise.

Write `T = B ∘ₗ A` for the supplied nonzero composite to the reversed standard module. The
reverse-kernel result makes `ker T` the largest proper stable subspace of the source.
`eq_ker_of_largest_proper` identifies it with `ker p`. Since `ker A ≤ ker T`, `p` descends
through `ker A`. The first isomorphism theorem identifies that quotient with `range A`.
Surjectivity and equivariance follow by evaluating on the elements `A x` of the range.

This is an internal reduction for the archimedean constituent step in Getz–Hahn,
*Automorphic Representations* (2024), Theorems 10.6.4 and 10.7.5, printed pp. 286 and 288
(PDF pp. 298 and 300 of the registered source `getz-hahn-2024-automorphic-representations`).
Knapp (1994), Theorems 1(a) and 4(a), printed pp. 400 and 405 (PDF pp. 410 and 415
of `knapp-1994-archimedean-llc`), gives the irreducible quotient of an ordered standard module.
The Lean argument takes that quotient and a nonzero factored reverse intertwiner as inputs.
