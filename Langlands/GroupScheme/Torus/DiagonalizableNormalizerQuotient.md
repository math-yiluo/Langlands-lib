# Smooth quasi-affine quotients by diagonalizable normalizers over rings

For every commutative ring `R`, finitely generated abelian group `M`, smooth
relatively affine group `G` over `Spec R`, closed embedding `i : D_R(M) → G`,
and supplied representative `n : N → G` of the full normalizer of `i`, this
module constructs an actual `HomogeneousQuotient n`. Its structure morphism
is smooth, and its underlying scheme is quasi-affine.

`diagonalizableNormalizer_exists_smooth_quasiAffine_quotient_overRing` gives
the existence theorem with both properties.
`diagonalizableNormalizer_exists_quasiAffine_quotient_overRing` is the
weaker interface needed by general-base descent.
`diagonalizableNormalizerQuotientOverRing` chooses the actual quotient and
retains both properties. There are no additional hypotheses on the base
ring, no split smoothness condition on `D_R(M)`, and no unproved local-model
input.

The implemented proof has four steps.

1. The normalizer-smoothness theorem applies to the supplied representative
   `n`. Its closedness is transported from the existing chosen closed
   normalizer through the unique isomorphism of representatives.
2. `finiteTorsionNormalizerOverRing` chooses a positive integer `m` such
   that the closed finite subgroup `D_R(M/mM)` has exactly the same full
   normalizer subgroup functor as `D_R(M)`. The quotient character group is
   finite by `FiniteCharacterSeparation.finite_quotient`.
3. The finite diagonalizable orbit construction supplies an actual
   quasi-affine target for the conjugation orbit of that finite subgroup,
   with exactly its full normalizer cosets as fibers on all relative
   scheme tests. Equality of the two normalizer functors and the supplied
   representing property of `n` transfer that exact fiber criterion to
   `SubgroupFunctor.range n`.
4. The quasi-affine-target homogeneous orbit theorem applies to the closed
   smooth subgroup `n`, yielding the actual smooth homogeneous quotient
   and quasi-affineness.

All provenance is derived from the imported finite-torsion detection,
closed-embedding quotient, normalizer-smoothness, and homogeneous orbit
constructions. This proves the complete split affine-base normalizer
quotient input; descent to arbitrary bases and the separate Weyl-group
clause are assembled elsewhere.
