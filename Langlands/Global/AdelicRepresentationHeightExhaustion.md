# Compact exhaustions by full adelic representation height

Author: Worker 94.

Fix a number field `F : Type u`, a group scheme `G` over `Spec F`, and a
matrix representation `rho` of rank `N`. All sets in this module are subsets
of the existing `AdelicGroupPoints F G`, with its original evaluation topology.
The height is exactly the published `RepresentationGrowth.adelicHeight F G rho`,
the dimension-scaled product of the matrix-and-inverse factors at all places.

`adelicHeightSublevel F G rho B` is the set of actual adelic points with height
at most the real number `B`. Its membership formula and monotonicity are
immediate. Inversion preserves every sublevel, by the existing
`adelicHeight_inv`. At positive rank, multiplication takes the sublevels at
`B` and `C` into the sublevel at `B * C`. The proof uses the existing
submultiplicative height inequality and the lower bound one to justify
multiplication of the inequalities; `B` and `C` need no sign assumptions.
Both pointwise membership and the set product inclusion are exported.

`exists_nat_adelicHeight_bound_of_isCompact` says that every compact subset
has height bounded by a natural number. Continuity of the positive-rank
height makes its image bounded above, and the Archimedean property supplies
a larger natural number. This result needs neither affineness of `G` nor
closedness of `rho`.

Now assume `G` is affine, `N > 0`, and `GroupScheme.IsClosedSubgroup rho`,
the existing scheme-theoretic closed-immersion condition.
`isCompact_adelicHeightSublevel` proves compactness of every real sublevel:
the height is at least one, so that sublevel equals the preimage of the
compact interval `[1, B]` under the published proper height map. This also
covers `B < 1`, where the interval and sublevel are empty.

`adelicHeightCompactExhaustion F G rho hN hrho` is a Mathlib
`CompactExhaustion` whose level `n` is exactly `adelicHeightSublevel F G rho n`.
Every level is compact by the preceding result. The open strict sublevel at
`n + 1` contains level `n` and lies in level `n + 1`, proving inclusion in
the latter's interior. Every point has height less than a natural number,
so the union of the levels is the whole original adelic point space.
The module exports the exact level and membership formulas, invariance of
each level under inversion, and the inclusion of the product of levels
`m` and `n` in level `m * n`.

`exists_adelicHeightCompactExhaustion_superset` places every compact set in
some level. For any second positive-rank closed matrix embedding `sigma`
of the same affine group, `adelicHeightSublevel_subset_other_exhaustion`
places each real `rho`-sublevel in a natural `sigma`-level.
`adelicHeightCompactExhaustion_cofinal` specializes this to the natural
levels; exchanging `rho` and `sigma` gives the reverse cofinality.
This uses compactness of the source sublevel and continuity of the target
height. It asserts no numerical polynomial comparison.

The provenance is internal. The construction consumes the published
continuity and properness results from
`AdelicRepresentationHeightPropernessProof`, the lower bound, inversion and
product laws from `AdelicRepresentationHeight`, and Mathlib's compact
exhaustion interface. It introduces no new assertion from the literature.
It does not construct an embedding or a split component, descend the
height to a rational or split-centre quotient, or prove a Siegel-set,
reduction, finite-volume, or automorphic integrability theorem. These
ambient compact exhaustions retain the task's separate quotient and
reduction obligations.
