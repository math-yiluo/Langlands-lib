# Actual local-model points at an adelic level

This unit constructs coordinate restriction maps for both actual number-field
adelic levels and actual curve-place adelic levels. These are arithmetic
specializations of the published relative scheme-point and local-base-change
constructions, with explicit original scalar actions.

For fields `k` and `F` in one arbitrary universe with `Algebra k F`,
`CurvePlaceLevelFactorIndex k F S` is the disjoint sum of actual curve places
in the finite set `S` and those outside it. `CurvePlaceLevelFactor` assigns
the published adic completion to a place in `S` and its published completed
valuation ring to a place outside `S`. For a number field `K` in an arbitrary
universe, `NumberFieldLevelFactorIndex K S` additionally includes every
infinite place. Its corresponding factors are the existing infinite
completions, the finite completions in `S`, and the completed valuation
rings at finite places outside `S`. The ring, topological-space,
topological-ring and local-ring instances are the existing ones on each
factor. No topology on a completion is replaced.

`curvePlaceLevelFactorRingEquiv` and `numberFieldLevelFactorRingEquiv`
reindex the published level product ring equivalences as single dependent
products. Their coordinate projections induce scalar actions from the
original `curvePlaceSIntegers` or Mathlib S-integer ring by composing with
the original published level diagonal. The `..._algebraMap_...` lemmas
show that these actions, including those on the integral factors, are
exactly the original global-field embeddings. The corresponding
`...LevelFactorAlgEquiv` and `...LevelFactorAlgHom` respect those actions.
The coordinate projection formulas recover the literal original adelic
coordinates.

For any scheme `X` over the relevant S-integer ring, without affineness or
finiteness assumptions, `curvePlaceLevelModelPointMap` and
`numberFieldLevelModelPointMap` send an actual level-valued relative point
to a family of actual points of the actual local base changes of `X`.
Each component is precomposition with the spectrum of the coordinate
algebra homomorphism followed by `ringPointBaseChangeEquiv`, the published
pullback-adjunction equivalence. The `..._left_fst` identity identifies
projection to the original model with precisely this coordinate
restriction.

The generic `ringPointChangeRingEquiv` constructs inverse coefficient
changes along an algebra equivalence; the inverse laws follow from
composition of spectrum maps. Each `...ModelPointMap_eq` proves that the
arithmetic map equals the existing `localProductPointMap` after this
explicit coefficient equivalence. Thus the comparison is attached to the
actual point map rather than to an assumed point-comparison structure.

The provenance is derived implementation infrastructure for Conrad's
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Theorem 3.6 and formula (3.6.1), printed pages 6–7, using the level and
S-integer conventions on printed page 1. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The single sum index is an implementation of the source's product of
products; it introduces no additional factors.

This definition unit proves the intrinsic algebra and coordinate identities
above. It does not prove that either model-point map is bijective or a
homeomorphism. Those conclusions require separate targets and proofs.
The curve-place construction does not yet assume a global function field.
It therefore specializes to actual global function fields without
requiring separability or infinite constants. Arithmetic realization,
Noetherianity of the S-integer base, the finite-type consequences needed
for the nonaffine comparison, model descent, transition maps, and
independence of the initial model remain separate obligations.
The constructions allow any finite `S`; applying them with Conrad's
conventions requires nonempty `S` in the function-field case.
All infinite places are included in the number-field construction,
including when the finite-place set is empty.
