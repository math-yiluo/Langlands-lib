# Point groups of unipotent groups in prime characteristic

Worker 302 supplies an internal adapter from the published uniform exponent
theorem to Mathlib's abstract `IsPGroup` predicate. All declarations work at
an arbitrary universe `u`.

Let `k` be a field of prime characteristic `p`, and let `U` be an affine
locally finite type unipotent group scheme over `k`. For every scheme `T`
over `k`, `isPGroup_testPoints_of_isUnipotent` proves that the actual group
of `T`-valued points of `U` is a `p`-group. No finiteness of `k` or `T`,
smoothness or connectedness is assumed.

The implemented proof applies
`exists_hasUniformPowerExponent_of_isUnipotent` from
`Rational.UnipotentPointsExponent`. Its single exponent `p^r` kills every
test point. The characterization `isPGroup_iff_pow_pow_eq_one` then gives
`IsPGroup` directly.

The second theorem treats the actual pointwise range of any group-scheme
homomorphism `U ⟶ G`. This range is the carrier of
`SubgroupFunctor.range` at `T`. The range restriction of the induced point
homomorphism is surjective, so Mathlib's `IsPGroup.of_surjective` transfers
the first theorem to that image.

`unipotentPointPSubgroup` bundles this actual range subgroup with its proved
`IsPGroup` property in the subtype of `p`-subgroups. Its value projection is
definitionally the existing range carrier, as the final simplification
lemma records. The bundle makes no choice of a Sylow overgroup.

The provenance is internal: both conclusions are direct consequences of
the named published exponent result and the abstract group lemmas. This
module supplies neither the pro-`p` property of an integral-model reduction
kernel nor a Sylow or Borel classification.
