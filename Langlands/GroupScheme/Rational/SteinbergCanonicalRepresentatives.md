# Simple-reflection representatives determined by normalized root coordinates

This internal construction starts with an affine group scheme over an arbitrary
field, a supplied `SplitPinning p`, and supplied normalized simple-root
parametrizations. It constructs actual simple-reflection representatives from
these data. It does not assert existence or Galois compatibility of the supplied
pinning or parametrizations.

For a normalized root map `x`, `unitPoint` is its rational point with coordinate
one. The definition uses the inverse of the actual global-sections isomorphism
of `Spec k`, as in `RootParametrization.rationalPoint`. The theorem
`unitPoint_eq` identifies it with `x.point` evaluated at the global section one.
The represented-root-subgroup property proves membership in the positive
intrinsic root group. Injectivity of the root parametrization, already proved
in `SteinbergModifiedRootProduct`, proves that this point is not the identity:
the scalar one is nonzero over every field, including fields with two elements.

The published theorem `splitPinnedOppositeFactorPairs` supplies an ordered
pair of actual negative-root points around `unitPoint` whose triple normalizes
the supplied torus. The construction chooses this pair as `oppositeFactorPair`
and records all its conditions in `oppositeFactorPair_spec`.
`eq_oppositeFactorPair` applies the proved uniqueness theorem for actual
opposite pairs to show that every such ordered pair is this pair. Thus its
point values are determined by the supplied normalized root map.

`reflectionRepresentative` uses the triple consisting of the first opposite
point, `unitPoint`, and the second opposite point. Its torus automorphism is
`normalizingAut`, with normalization proved by
`isNormalizingPoint_normalizingAut`. The imported theorem
`SplitPinning.oppositeFactorPair_weylAction` identifies its action with the
pinned root-datum reflection on the whole integral character lattice. This
proves the full `SimpleReflectionRepresentative` fields, rather than only the
negation of the chosen root.

Each of the triple's factors belongs to either the positive or negative root
point subgroup. Closure under multiplication therefore proves
`reflectionRepresentative_mem_generated`. Applying the construction to every
supplied simple-root map gives `canonicalSimpleReflectionRepresentatives` and
proves `RootGeneratedSimpleReflectionRepresentatives` for that family.
`commute_canonicalRootFactors` then specializes the proved all-test orthogonal
factor theorem: factors from distinct orthogonal roots in this same supplied
simple-root base commute on every scheme test and for every global scalar.

The provenance is an internal deduction from published actual opposite-pair
existence and uniqueness, the exact reflection comparison, and the existing
normalized-root and commutation interfaces. It introduces no original-source
assertion. No perfectness, infinitude, characteristic, semisimplicity, or
simply connectedness hypothesis is added beyond the supplied split pinning
and normalized maps, and the universe is arbitrary. Compatibility under a
Galois action, existence of compatible root maps, orbit blocks, immersion,
regularity, the canonical quotient comparison, exceptional even-type-A
geometry, and rational lifting remain separate obligations of the parent task.
