# Uniform compact bounds for the actual positive parts

This internal bridge supports the bounded-region step of Waldspurger (2003),
Lemma VI.2.3, printed p.301. It derives compact bounds for the existing
`positivePart` from the previously implemented uniform annihilators and the
published finite-translate bound for the weak part. The registered source is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The results are internal algebraic and topological interfaces derived from the
current Library, rather than a new literal source statement.

`HasUniformWeightedCompactBounds F B` means that on each compact subset of the
group a single positive constant bounds every member of `F` by that multiple of
`B`. The property pulls back along any continuous map, including an actual
subgroup inclusion; the positive part can be formed on the original group
before this restriction. A jointly continuous family indexed by a compact space has this property
for a continuous everywhere-positive weight, by bounding the continuous ratio
of the norm and weight on a product of compact sets.

`continuous_uncurry_of_uniform_right_invariance` supplies joint continuity
from continuity in the parameter at each fixed group point and invariance
under one common open right-translation subgroup `U`. At a group point `g`,
the open left coset `gU`, described by `g⁻¹ * x ∈ U`, is a neighborhood on which
each family member is constant in the group variable. On this neighborhood
the family therefore depends only on its parameter.

The positive-part transfer uses monic annihilators of fixed degrees with the
uniform root gap from `HasUniformSplitAnnihilators`. On a compact set `Q`, the
published `exists_norm_le_sum_translates` bounds the actual weak part by a
uniform finite sum of translates of the full function. The finitely many
translates of `Q` form another compact set. The common weight is assumed
invariant under the selected translation. Compact bounds for
the full family therefore bound the weak part, and subtraction bounds the
actual positive part. No continuity of the weak or positive part is required
for this transfer, and no generic-parameter restriction is imposed.

The unit does not establish these premises for the actual induced orbit.
