# Dominant nonfixed orbits on schemes of dimension at most one

This internal helper turns nonfixedness of a rational section into dominance
of its actual scheme orbit, when the target is irreducible and has topological
Krull dimension at most one. It also supplies quasi-compactness for a smooth
connected affine acting group. The field can have any characteristic.

## A topological lemma

`Langlands.Topology.dense_of_isIrreducible_of_two_points_of_dimension_le_one`
works in an arbitrary universe `v`. Let `X` be an irreducible topological
space with `topologicalKrullDim X ≤ 1`. If an irreducible subset `s` contains
distinct points `x` and `y` and the singleton `{x}` is closed, then `s` is
dense in `X`. No separation or Noetherian hypothesis is imposed.

The proof sets `Z = closure s` and regards `Z` and `{x}` as elements of the
ordered set of irreducible closed subsets of `X`. The strict containment
`{x} < Z`, witnessed by `y`, means that `Z` is not minimal. Mathlib's
`Order.krullDim_le_one_iff` says that every irreducible closed subset is
minimal or maximal, so `Z` is maximal. Irreducibility of `X` makes the whole
space an irreducible closed subset containing `Z`. Maximality therefore
gives `Z = X`, which is the required density.

## Dominance of a nonfixed orbit

In namespace `Langlands.GroupScheme.SchemeAction`,
`nonfixedRationalTranslate` first constructs a rational section `h` of a
smooth group `H` with `a.act h x ≠ x`, from a supplied nonfixed rational
section `x` of a separated locally finite type scheme over an algebraically
closed field. It returns `h` together with this inequality. The construction
uses classical choice and the published rational-point fixedness criterion.
It requires neither irreducibility nor a dimension bound.

In the same namespace,
`isDominant_orbitMap_of_not_isFixed_of_dimension_le_one` has these inputs:

- an algebraically closed field `k : Type u`;
- an actual action `a : SchemeAction H X`;
- a smooth group scheme `H` over `k` whose underlying space is irreducible;
- an irreducible scheme `X` locally of finite type and separated over `k`;
- `topologicalKrullDim X.left ≤ 1`;
- a rational section `x` that is not fixed by `a` on all scheme tests.

Its conclusion is `IsDominant (a.orbitMap x).left`, for the actual orbit
morphism from the underlying scheme of `H` to `X`.

The proof uses `nonfixedRationalTranslate` to choose `h`. The rational sections
`x` and `a.act h x` correspond to distinct closed underlying points, by
injectivity of `rationalPointEquivClosedPoint`. Both lie in the range of the
actual orbit morphism: the first via the identity, the second via `h`, using
`mem_rationalOrbit_iff`. That range is irreducible because it is the
continuous image of the irreducible space of `H`. The topological lemma
then makes the range dense, giving dominance.

## The connected affine case

`dominant_quasiCompact_orbitMap_of_not_isFixed_of_dimension_le_one` replaces
irreducibility of `H` with the assumptions that `H` is smooth, connected,
and affine over `k`. All the other hypotheses above remain. It proves
both dominance and quasi-compactness of the same actual orbit morphism.

The published `smoothConnectedAffineGeometry` theorem makes `H`
geometrically integral, hence irreducible over the field, so the preceding
theorem supplies dominance. The composite of the orbit morphism with the
structure map of `X` is the affine structure map of `H`, hence is
quasi-compact. `QuasiCompact.of_comp` then gives quasi-compactness of the
orbit morphism. Separatedness of `X` provides the needed quasi-separatedness.

## Provenance and remaining application

This is an internal derivation from the published actual-action interfaces,
the rational-section/closed-point equivalence, smooth connected affine group
geometry, and Mathlib's order-theoretic characterization of dimension at
most one. It claims no new external source theorem. Worker 1547 developed
the proof to supply the orbit step of the prescribed-Borel route discussed
with Worker 317.

The exact `RankOnePositiveRootUniquenessStatement` remains open. This module
does not construct a Borel quotient, prove that it is an irreducible curve,
or produce a nonfixed rational section for a particular dynamic subgroup.
Those are inputs to a later application. It also does not prove the
normal-solvable-torus theorem or any dimension-to-root comparison. The
target is allowed to be nonreduced here; any reducedness needed for a later
action-kernel argument must be established separately.
