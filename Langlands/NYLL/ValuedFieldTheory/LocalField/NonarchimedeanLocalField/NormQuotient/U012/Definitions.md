# Equal norm subgroups identify norm quotients

This module defines
`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfNormSubgroupEq`, the
canonical multiplicative equivalence between two norm quotients of the
same base field whose norm subgroups are equal. It is the data definition
M093.012 in the [NYLL declaration partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

## Complete interface

Inside `namespace Langlands.NYLL.LocalFieldTheory`, the complete telescope
and result are:

```lean
normQuotientEquivOfNormSubgroupEq.{u}
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M) :
    NormQuotient K L ≃* NormQuotient K M
```

There is one arbitrary universe parameter, `u`, shared by all three
fields. The fields and equality `h` are explicit arguments; the three
field structures and two algebra structures are instance-implicit
arguments. There are nine binders in total. This is a definition of data,
with result a multiplicative equivalence, rather than a `Prop` target.

No finite-dimensionality, separability, Galois, local-field, valuation,
topology, surjectivity or exact-kernel premise is imposed. No algebra
structure relating `L` to `M` is needed: the comparison takes place in
the common ambient group `Kˣ`.

## Actual norms and quotients

The unchanged published dependencies define:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
```

The analogous equations hold with `M` in place of `L`. Thus `h` equates
the actual images of the unit norm maps `Lˣ →* Kˣ` and `Mˣ →* Kˣ`.
The result compares the quotients of `Kˣ` by these very subgroups.
The source and target multiplication structures come from the respective
published `normQuotientCommGroup` instances; both are the usual coset
multiplication.

The norm here is Mathlib's general `Algebra.norm K`. In the approved
`Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62 define it as the
determinant of left multiplication, without a finite-module premise.
Lines 76–79 prove `Algebra.norm_eq_one_of_not_module_finite`: when the
algebra is not a finite module over the base, this general norm is
constantly `1`. Consequently its restriction to units is constantly the
unit `1`, and its range is the trivial subgroup. This convention applies
separately to `L/K` and `M/K`. In particular, if both modules are
nonfinite, both subgroups are trivial; if only one is nonfinite, `h`
requires the other norm image to be trivial as well. The construction
uses the supplied equality in every case and does not assume that this
general norm has the additional properties of a finite extension norm.

## Canonical construction and representatives

The implementation is exactly the original two-step body:

```lean
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ localNormSubgroup K M)
  exact QuotientGroup.quotientMulEquivOfEq h
```

The first step exposes both named quotients. Their multiplication
structures are definitionally those of the concrete quotient groups, so
`change` preserves the goal. The second step uses
`QuotientGroup.quotientMulEquivOfEq` from the approved
`Mathlib/GroupTheory/QuotientGroup/Basic.lean`, lines 162–168.
Normality is inferred for both subgroups because `Kˣ` is commutative,
using `Subgroup.normal_of_isMulCommutative`
(`Mathlib/Algebra/Group/Subgroup/Defs.lean`, lines 629–631).
No normality argument is added to the telescope.

Mathlib constructs this multiplicative equivalence from
`Subgroup.quotientEquivOfEq h`
(`Mathlib/GroupTheory/Coset/Defs.lean`, lines 266–272). Its forward and
inverse maps are `Quotient.map' id` with the relation proofs transported
along `h` and `h.symm`, respectively. Both maps therefore preserve
base-field unit representatives: the forward map sends `normClass K L x`
to `normClass K M x`, and the inverse sends `normClass K M x` to
`normClass K L x`. The relation is respected because the subgroups are
equal; the inverse identities and multiplication law follow by quotient
induction. Mathlib's `quotientMulEquivOfEq_mk` at lines 170–173 records the
forward computation by `rfl`. The inverse computation also reduces to
`rfl` on representatives.

The definition retains the source's `noncomputable section`. It does
not choose representatives or replace either quotient. M093.013 is the
separate public representative-evaluation unit, to be handled by its own
published `Prop` target and subsequent proof. This candidate adds only
the data definition; no instance or simp registration is added.

## Original source and adaptation

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
lines 115–122: the docstring is line 115, the declaration is lines 116–120,
and its body is lines 121–122. The entire source file has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Lines 1–166 were read for this extraction, including the subgroup and
quotient definitions, the predecessor and the separately reserved
evaluation theorem at lines 124–135.

The retained original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
The registered supplement
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`,
retains additional attribution files. The source-ID errata locations in
the workspace, project and current Library were checked; no applicable
erratum was found.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normQuotientEquivOfNormSubgroupEq` | `Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfNormSubgroupEq` |

Only the namespace prefix changes in the declaration: its parameter
order, binder kinds, result, docstring and body are preserved verbatim.
The source's unused universe `v` is omitted. The source's imports are
replaced with the single direct import
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U011.Proofs`,
preserving the partition's `M093.011.END` dependency. This published
chain supplies the original definitions under `Langlands.NYLL` and the
required Mathlib quotient API. All 16 imported Library modules and
their same-stem Markdown companions are unchanged. The partition records
no patch10 change to this module.

Fresh TaskHub and exact-name Lean searches of the workspace, current
Library, staged candidates, approved Mathlib and shared drafts found no
duplicate task or published definition. The only older shared-draft
matches are upstream copies in the source-audit task; none was reused.
Worker 107 extracted this unit directly from the pinned original and
wrote this companion. There are no other project coauthors of this unit.

## Attribution and scope

The original 2026 Naganori Yamaguchi copyright and author header is
retained verbatim, including “Naganori Yamaguchi (assisted by OpenAI
Codex)”. An explicit modification record identifies Worker 107's
extraction, namespacing and import changes on 30 October 2026.
The unchanged Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included in the
submission's `repository_paths`. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`;
both match the originals. The original NOTICE has no NormQuotient entry,
and the supplement's ValuedFieldTheory table of included Anthropic FLT
sources does not list this file. Existing dependency attribution is
preserved.

This generic algebraic transport supplies no named Artin map,
norm-kernel theorem, host quotient or evaluation adapter, topology or
continuity result. Those are separate obligations of the parent finite
reciprocity task, which remains open.
