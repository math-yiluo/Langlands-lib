# Membership in the norm-class kernel

This module proves the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassMemKerIffStatement.{u}` by
`Langlands.NYLL.LocalFieldTheory.normClass_mem_ker_iff.{u}`.
A base-field unit belongs to the kernel of the canonical norm-class
homomorphism exactly when it is the norm of an extension unit.
This is the proof phase of M093.021 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

## Complete closed target and theorem

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U021.Statements`.
The published statement and all imported Lean/Markdown pairs are unchanged.
In namespace `Langlands.NYLL.LocalFieldTheory`, the complete interface is:

```lean
def NormClassMemKerIffStatement.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ),
    x ∈ MonoidHom.ker (normClass K L) ↔ x ∈ localNormSubgroup K L

theorem normClass_mem_ker_iff.{u} : NormClassMemKerIffStatement.{u}
```

The theorem's unapplied type is exactly the named closed proposition.
It has no external term parameters. Its sole universe parameter `u`
is arbitrary and shared by `K` and `L`. All six term binders occur
inside the proposition, in this order:

| Position | Binder | Kind |
| --- | --- | --- |
| 1 | `K : Type u` | Explicit base-field type |
| 2 | `L : Type u` | Explicit extension-field type |
| 3 | `[Field K]` | Instance-implicit field structure |
| 4 | `[Field L]` | Instance-implicit field structure |
| 5 | `[Algebra K L]` | Instance-implicit algebra structure |
| 6 | `x : Kˣ` | Explicit base-field unit |

Applying `normClass_mem_ker_iff K L x` obtains the equivalence, with
the three structures inferred as instances. There is no added
finite-dimensionality, finite-module, local-field, separability,
Galois, valuation, topology or other premise.

## Actual norm image and canonical quotient

The theorem uses the existing published constructions:

```lean
normUnits K L : Lˣ →* Kˣ
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

The norm runs from extension units to base-field units. Membership
in its actual range means that some `y : Lˣ` satisfies
`normUnits K L y = x`. The named quotient divides base-field units
by this image subgroup. The canonical class map is
`QuotientGroup.mk' (localNormSubgroup K L)`, expressed through the
named quotient and its published `normQuotientCommGroup K L`
structure. Kernel membership means `normClass K L x = 1`.

Mathlib defines `Algebra.norm K` as the determinant of multiplication
in `Mathlib/RingTheory/Norm/Defs.lean:59–62`.
`Algebra.norm_eq_one_of_not_module_finite` at lines 76–79 makes this
norm constantly `1` when `L` is not a finite `K`-module. Then all unit
norms are `1` and their range is the identity subgroup. The theorem
includes these algebras with Mathlib's convention.

## Implemented proof

The complete proof is:

```lean
by
  intro K L _ _ _ x
  rw [normClass_ker K L]
```

The introductions unfold the closed target and introduce its six
internal binders. The three anonymous binders install the field and
algebra structures as instances. The published predecessor
`normClass_ker K L` identifies
`MonoidHom.ker (normClass K L)` with `localNormSubgroup K L`.
Rewriting the left membership proposition by this subgroup equality
leaves an equivalence of that proposition with itself, which `rw`
closes by reflexivity.

This is the original proof at line 204, preceded by the introductions
needed for the closed Library target. The predecessor is available
through U021.Statements' sole import of U020.Proofs; it proves its
kernel equality using Mathlib's `QuotientGroup.ker_mk'`.
No helper declaration or alternate norm, subgroup, quotient or map
is introduced.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:199–204`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L199-L204):
docstring at lines 199–200, theorem name and telescope at lines
201–202, conclusion at line 203 and rewrite proof at line 204.
The complete original was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The norm subgroup, quotient and class map are defined at lines 26–54.
The original unit norm is defined in
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normClass_mem_ker_iff` | `normClass_mem_ker_iff : NormClassMemKerIffStatement.{u}` |
| Original telescope and conclusion | Existing closed `NormClassMemKerIffStatement.{u}` |
| `normClass_ker` | Existing `normClass_ker` in U020.Proofs |
| `normUnits` | Existing `normUnits` |
| `localNormSubgroup` | Existing `localNormSubgroup` |
| `NormQuotient` | Existing `NormQuotient` |
| `normQuotientCommGroup` | Existing `normQuotientCommGroup` |
| `normClass` | Existing `normClass` |

Only the first row adds a declaration. Worker 1153's modification on
1 November 2026 adds the namespace prefix, uses the published closed
target, introduces its six binders and retains the original rewrite.
The sole direct import is U021.Statements. The source noncomputable
section, unused universe `v` and all other declarations are omitted.
M093 has no compatibility change in the feasibility patch10.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution material
is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source-ID errata locations in the workspace, project and supplied
Library were checked; none exists.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Upstream used Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and scope

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi, released under Apache-2.0, author
Naganori Yamaguchi (assisted by OpenAI Codex). The Lean file includes
the dated modification record. Worker 1153 extracted the proof from
the pinned original and wrote this companion. Worker 107's published
statement and predecessor proof are imported unchanged; no worker
proof draft or patch10 edit was reused.

The inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained
unchanged in `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Existing dependency attribution remains intact.

This generic canonical-quotient membership equivalence leaves parent
task `1cbd1968-d285-4b34-822c-f6b5599d1c38`'s named Artin kernel and
surjectivity, actual host quotient and evaluation, and topology
obligations open. M093.022 and later units remain separate.
Development compilation is separate from independent semantic
acceptance and Integrator publication.
