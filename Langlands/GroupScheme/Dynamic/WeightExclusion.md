# Weight signs in actual Lie images of dynamic parabolics

This internal helper derives weight-sign consequences from the published theorem
`dynamicLie`. It concerns an affine group scheme `G` locally of finite type
over any field `k : Type u`, a split torus `T`, a homomorphism `j : T ⟶ G`,
and a cocharacter `ν` of `T`. No reductivity, maximality or regularity is required.

`mem_nonnegativeWeightSpan_iff_mem_parabolic` identifies membership of an actual
dual-number identity-kernel point in `Dynamic.parabolic (ν ≫ j)` with membership
of its additive Lie vector in `nonnegativeWeightSpan j ν`. The proof combines
the parabolic clause of `dynamicLie` with the published regrouping of
cocharacter weights into character weights in `RegularCocharacterWeights`.
It uses no theorem identifying general Borel subgroups with dynamic parabolics.

`latticePairing_nonneg_of_weight_mem_parabolic` takes a nonzero vector in
`weightSpace j α` whose dual-number point belongs to this dynamic parabolic.
It proves `0 ≤ latticePairing T α ν`. If the pairing were negative, the
published direct-sum decomposition for split-torus weights would make
`weightSpace j α` disjoint from the nonnegative weight span. Their common
vector would be zero, contradicting the hypothesis.

`latticePairing_nonneg_of_lieImage_range_le_parabolic` applies this result to
the actual Lie image of an arbitrary homomorphism `i : H ⟶ G` satisfying
`SubgroupFunctor.range i ≤ Dynamic.parabolic (ν ≫ j)`. The actual dual-number
preimage gives range membership on the same test scheme. There are no
smoothness, affineness, closedness or monomorphism assumptions on `H` or `i`.

Finally, `not_meets_oppositeWeightSpaces_of_range_le_parabolic` excludes a pair
of nonzero Lie-image witnesses of weights `α` and `-α` when
`latticePairing T α ν ≠ 0`. Applying nonnegativity to both weights gives a
nonnegative integer and its nonnegative negative; hence the pairing is zero,
a contradiction. Both existential clauses use exactly the actual
dual-number-point form of `RankOneSolvableObstructionStatement`.

The module supplies only the consequence of a given dynamic-parabolic
containment. Constructing that containment for a Borel or for a general
solvable subgroup remains a geometric proof obligation. All arguments work
in every characteristic. The provenance is internal: the proof uses the
published dynamic Lie theorem, split-torus weight decomposition and lattice
pairing, and does not introduce an external structural assertion.
