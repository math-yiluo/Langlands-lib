# NYLL M120.082: quotient-image membership target

For an antitone subgroup filtration `U` of an arbitrary group `G`, indices
`m ≤ n`, and normality of both filtration levels, the class of `x` in
`G ⧸ U.principalUnitSubgroup n` belongs to the image of level `m` if and only
if `x` belongs to level `m`.

## Original source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean`,
M120.082, declaration at line 1059, telescope and proposition at lines
1060–1066, original proof at lines 1067–1072.
The source file SHA-256 is
`30ce59edb8590e15afdaaef8d9551282e240c576f09be0ad55d12b09e9e4d807`.

The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original declaration is
`LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.quotient_principalUnitSubgroup_mk_mem_classInQuotient_iff`.
Its adapted target is
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.quotient_principalUnitSubgroup_mk_mem_classInQuotient_iffStatement`.

## Exact statement and shared objects

The full telescope is `{G : Type u} [Group G]`
`(U : AntitoneSubgroupFiltration G) {m n : ℕ} (_hmn : m ≤ n)`,
followed in order by `[(U.principalUnitSubgroup n).Normal]`,
`[(U.principalUnitSubgroup m).Normal]`, and `(x : G)`.
The source's carrier universe `u` and unused universe declaration `v` are
retained. The order proof is an explicit parameter even though the
proposition body does not mention its proof term. Normality at level `m`
is retained from the source.

The proposition is exactly
`QuotientGroup.mk' (U.principalUnitSubgroup n) x ∈
U.principalUnitSubgroupClassInQuotient m n ↔
x ∈ U.principalUnitSubgroup m`.
It uses the published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration`
and its `principalUnitSubgroup` accessor from
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Filtration`,
and its `principalUnitSubgroupClassInQuotient` from
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Subquotient`.
Those are the source M120.001, M120.002 and M120.024 objects. No duplicate
filtration, quotient image, or instance is introduced.

This source result is generic group theory. It asserts no intrinsic
valued-field or principal-unit semantics for an arbitrary filtration.
The concrete unit filtrations used by the Lubin–Tate route can instantiate
this shared generic statement.

## Modifications, attribution, and proof boundary

Worker 311 extracted the proposition into this focused module, prefixed
the source namespace by `Langlands.NYLL`, and replaced the source theorem
by a `Prop`-valued definition with the suffix `Statement`. The unused
source hypothesis binder `hmn` is renamed `_hmn`, without changing its
type, position or explicitness. The docstring and module comment describe
the target. The import is the published quotient-data module rather than
the source file's original Mathlib imports; its import chain supplies
the required Mathlib objects. No other statement parameter or hypothesis
is changed, and no theorem or instance is added.

This file states M120.082; it does not publish a proof. The private proof
route uses Mathlib `QuotientGroup.comap_map_mk'`, the stored antitone law,
and `sup_eq_right`. Thus it can avoid the source's level-change-map kernel
lemmas. Any proof publication must target this exact published proposition
and document its implemented route independently.

The original copyright and author header is retained verbatim. The
existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` retain the
Apache-2.0 license and attribution.
