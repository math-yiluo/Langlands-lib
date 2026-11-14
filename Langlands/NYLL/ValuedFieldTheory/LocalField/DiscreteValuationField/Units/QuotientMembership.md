# NYLL M120.082: quotient-image membership proof

For an antitone subgroup filtration `U` of a group `G`, with `m ≤ n`
and both levels normal, the class of `x` modulo level `n` belongs to
the image of level `m` exactly when `x` belongs to level `m`.

## Target and parameters

The theorem
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.quotient_principalUnitSubgroup_mk_mem_classInQuotient_iff`
proves the published proposition
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.quotient_principalUnitSubgroup_mk_mem_classInQuotient_iffStatement`,
imported from
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.QuotientMembershipStatement`.

The telescope is `{G : Type u} [Group G]`,
`(U : AntitoneSubgroupFiltration G) {m n : ℕ} (hmn : m ≤ n)`,
normality of `U.principalUnitSubgroup n`, normality of
`U.principalUnitSubgroup m`, and `(x : G)`, in that order.
The target is applied to `U`, `hmn`, and `x`; its implicit arguments and
normality instances are inferred from these same parameters.
The source universe `u` and unused universe declaration `v` are retained.
All shared filtration and image-subgroup objects are imported from the
published Library. No definition or instance is introduced.

## Implemented proof

Membership in the image of level `m` is definitionally membership in the
comap of that image along the canonical quotient homomorphism
`QuotientGroup.mk' (U.principalUnitSubgroup n)`. The first `change`
expresses the left side in this form.

Mathlib's `QuotientGroup.comap_map_mk'` identifies this comap with
`U.principalUnitSubgroup n ⊔ U.principalUnitSubgroup m`.
The stored antitone law applied to `hmn` gives
`U.principalUnitSubgroup n ≤ U.principalUnitSubgroup m`.
The intermediate inequality is explicitly typed using these accessors so
that `sup_eq_right.mpr hle` rewrites the displayed supremum. Both sides
then coincide, closing the equivalence.

The proof is generic group theory; no intrinsic valued-field structure
is asserted for an arbitrary antitone subgroup filtration.
It retains the target's level-`m` normality hypothesis even though this
direct argument needs only normality at level `n`.

## Provenance and modifications

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean`,
M120.082, declaration and proposition at lines 1059–1065 and proof at
lines 1066–1072. The source file SHA-256 is
`30ce59edb8590e15afdaaef8d9551282e240c576f09be0ad55d12b09e9e4d807`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Worker 311 extracted a focused module, added the `Langlands.NYLL`
namespace prefix, imported the published statement, and wrote the theorem's
type as that exact proposition. The source proof uses the kernel of a
level-change map and its formula on quotient representatives.
The implemented proof instead uses the Mathlib comap/map identity,
antitonicity, and the supremum identity, so it needs no source
level-change-map helpers. The theorem's source name and all its parameters
and hypotheses are preserved. The explanatory comments are new.
Worker 460 rechecked the Lean file unchanged against the published target
and submitted this pair.

The original copyright and author header is retained. The existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` supply the Apache-2.0
license and attribution.
