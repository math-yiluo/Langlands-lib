# Kernel of the norm-class homomorphism

This module defines the closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassKerStatement`.
It states that the kernel of the canonical homomorphism from base-field
units to their norm classes is the actual image of the algebra norm on
extension units. This is the statement phase of M093.020 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
The proposition definition supplies the target for a separate future proof.

## Complete closed proposition

In namespace `Langlands.NYLL.LocalFieldTheory`, the complete interface is

```lean
def NormClassKerStatement.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L],
    MonoidHom.ker (normClass K L) = localNormSubgroup K L
```

The unapplied declaration has type `Prop` and no external term parameters.
Its sole universe parameter `u` is arbitrary and shared by `K` and `L`;
it is not specialized to universe zero. All five source term binders
occur inside the defining universal quantifier, in exactly this order:

| Position | Binder | Kind and meaning |
| --- | --- | --- |
| 1 | `K : Type u` | Explicit base-field type |
| 2 | `L : Type u` | Explicit extension-field type |
| 3 | `[Field K]` | Instance-implicit field structure on `K` |
| 4 | `[Field L]` | Instance-implicit field structure on `L` |
| 5 | `[Algebra K L]` | Instance-implicit specified algebra structure |

The conclusion is equality of two subgroups of `Kˣ`. The left subgroup
is the kernel of the named `normClass K L`; the right subgroup is the
named `localNormSubgroup K L`. Equality asserts that precisely the
extension-unit norms have identity norm class. Given
`H : NormClassKerStatement.{u}`, clients obtain the subgroup equality
as `H K L`, with the three structures inferred as instances.

The telescope preserves the original unrestricted field/algebra
hypotheses. It adds no finite-dimensionality, finite-module,
separability, Galois, local-field, valuation, topology, surjectivity
or other premise.

## Actual norm image, quotient and kernel

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U019.Proofs`.
It retains the partition's published `M093.019.END` dependency boundary.
Through that import the proposition uses the existing constructions
unchanged:

```lean
normUnits K L : Lˣ →* Kˣ
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

Thus the norm is directed from extension units `Lˣ` to base-field units
`Kˣ`. The subgroup is its actual range: a unit `x : Kˣ` belongs to it
exactly when some `y : Lˣ` satisfies `normUnits K L y = x`.
The named quotient is base-field units modulo that image. The class
map is the canonical quotient homomorphism
`QuotientGroup.mk' (localNormSubgroup K L)`, expressed through the
named quotient. Its codomain carries the published
`normQuotientCommGroup K L` structure.

`MonoidHom.ker (normClass K L)` is the subgroup of units `x : Kˣ`
such that `normClass K L x = 1`, with identity taken in
`NormQuotient K L`. The proposition identifies this kernel with
the range subgroup above, using equality in `Subgroup Kˣ`.
It preserves both the named quotient and the actual canonical map.

In the approved Mathlib, `Algebra.norm K` is the determinant of
multiplication (`Mathlib/RingTheory/Norm/Defs.lean:59–62`).
`Algebra.norm_eq_one_of_not_module_finite` at lines 76–79 makes
the norm constantly `1` when `L` is not a finite `K`-module.
Consequently all unit norms are `1` in that case and their image
is the identity subgroup. The proposition continues to quantify
over such algebras with this convention.

## Pinned source and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:192–197`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L192-L197):
the docstring is line 192, the name and telescope are line 193,
the subgroup equality is line 194, and the proof is lines 195–197.
The complete original file was read and has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Its norm-subgroup, quotient and class-map definitions are at lines
26–54. The original unit norm is in
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`, SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normClass_ker` (theorem telescope and conclusion) | `NormClassKerStatement` (closed Prop definition) |
| `normUnits` | Existing `normUnits` |
| `localNormSubgroup` | Existing `localNormSubgroup` |
| `NormQuotient` | Existing `NormQuotient` |
| `normQuotientCommGroup` | Existing `normQuotientCommGroup` |
| `normClass` | Existing `normClass` |

Only the first row adds a declaration. Worker 107's modification on
1 November 2026 adds the namespace prefix, moves the original
theorem's complete telescope inside a closed `Prop` definition, and
replaces the original imports with the sole published U019 Proofs
import. Binder order, binder kinds, names, shared universe and
subgroup equality are preserved, as is the original docstring.
The source proof, noncomputable section, unused source universe `v`
and all other declarations are omitted. M093 has no compatibility
change in the feasibility patch10.

The retained original is in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source-ID errata locations in the workspace, project and supplied
Library were checked; none exists.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Statement boundary and attribution

This unit defines the proposition only. The theorem
`Langlands.NYLL.LocalFieldTheory.normClass_ker` and its exact proof
belong to a separate later unit after this target is independently
accepted and public. The original proof applies Mathlib's generic
`QuotientGroup.ker_mk'`; no proof of the proposition is supplied here.
M093.021 and all later units remain separate. Compilation and
inspection establish declaration shape; independent semantic review
and Integrator publication are separate requirements.

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi, released under Apache-2.0, author
Naganori Yamaguchi (assisted by OpenAI Codex). The Lean file includes
the dated modification record. Worker 107 extracted this statement
directly from the pinned original and wrote its companion; no worker
draft was reused. Published dependencies and their attribution
remain unchanged.

The inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included
unchanged in `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the retained upstream files. The inherited NOTICE's
ValuedFieldTheory list has no NormQuotient-specific third-party
entry; all existing dependency notices are preserved.

This generic canonical-quotient kernel statement leaves parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38`'s named Artin kernel and
surjectivity, actual host quotient and evaluation, and topology
obligations open.
