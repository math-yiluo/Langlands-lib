# Automatic reflection and uniqueness of actual opposite factor pairs

For an affine group scheme over an arbitrary field, an actual split torus
whose map to the group is monomorphic on underlying schemes, and a nonzero
character `a`, this module proves that every normalizing opposite pair of a
nonidentity point in the actual `a` subgroup sends `a` to `-a`. It constructs
the pair's actual integral coroot, proves its integral reflection formula,
and proves uniqueness of the pair. If `a` is a relative root, it also proves
the exact predicate `IsRelativeReflection` for the normalizer's class in the
existing relative Weyl group.

The provenance is an internal deduction from the full-kernel divisibility
theorem in [`RootKernelDivisibility`](RootKernelDivisibility.md), the
centralization and coroot construction in
[`RootFactorPairReflection`](RootFactorPairReflection.md), and actual
opposite-subgroup conjugation and separation in
[`RootSubgroupSeparation`](RootSubgroupSeparation.md). The argument supplies
the previously explicit root-flip premise; it uses no new external
structural assertion.

`weylAction_eq_self_or_neg_of_mem_kernelCentralizer` first treats a general
normalizer `n` centralizing the full character kernel. Full-kernel
divisibility for `n` and `n⁻¹` gives integers `m,m′` with
`w(a) = (1-m) • a` and `w⁻¹(a) = (1-m′) • a`. Their composite fixes `a`.
Pairing with a cocharacter having a strictly positive pairing with `a` and
cancelling this nonzero integer proves
`(1-m)(1-m′) = 1`. Thus `1-m` is either one or minus one. This general lemma
does not require affineness, finiteness of a Weyl group, or finite order of
its action.

`IsOppositeFactorPair.weylAction_ne_self` excludes the positive sign for a
normalizing opposite pair `p` of a nonidentity root point `x`. Write
`n = p.1 * x * p.2`. If `n` fixed `a`, then `n⁻¹` would fix `-a`, so
`q = n⁻¹ * p.1 * n` would belong to the actual opposite root subgroup by
normalizer conjugation. The equality
`n = x * (p.2 * q)` would express a normalizer as a product of one point
from each opposite direction. The published
`normalizer_eq_one_of_mul_opposite` forces `n = 1`; the resulting
`x * (p.2 * q) = 1` places `x` in the opposite subgroup too. Opposite
separation then gives `x = 1`, a contradiction.

The pair's three factors centralize the full character kernel by
`IsOppositeFactorPair.mem_kernelCentralizer`. The sign lemma and the
exclusion of the positive sign therefore prove
`IsOppositeFactorPair.weylAction_eq_neg`. Applying the published uniqueness
under a flip gives `IsOppositeFactorPair.eq` for any two such pairs. This
uniqueness compares every pair satisfying the original membership and
normalization conditions, without an additional condition on its action.

`IsOppositeFactorPair.coroot` uses this proved flip in `corootOfFlip` to
construct an actual cocharacter. `coroot_spec` gives self-pairing two and
the formula
`w(χ) = χ - ⟨χ, coroot⟩ • a`
on the whole integral character lattice. For membership of `a` in the
relative-root set, `IsOppositeFactorPair.isRelativeReflection` applies the
exact root-span reflection theorem to the same proved flip.

The results retain arbitrary universe, field and characteristic scope.
They require neither connectedness nor reductivity, neither maximality nor
primitivity of the torus character, and neither smoothness of its kernel
nor reducedness of the root system. They assume that the normalizing pair
has been supplied. Pair existence and the additional nonmultipliable-root
conclusions of `RootRankOneFactorizationStatement` remain open.
