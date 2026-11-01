# Norm classes of extension-unit norms

This module defines the closed proposition
`Langlands.NYLL.LocalFieldTheory.MkNormUnitsEqOneStatement`.
It states that, for every algebra `L` over a field `K`, the norm of
every unit of `L` has the identity class in the published norm
quotient `Langlands.NYLL.LocalFieldTheory.NormQuotient K L`.
This is the statement phase of M093.017 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Defining this proposition does not prove it.

## Complete closed interface

Inside `Langlands.NYLL.LocalFieldTheory`, the definition is:

```lean
def MkNormUnitsEqOneStatement.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ),
    normClass K L (normUnits K L x) = 1
```

The unapplied declaration has type `Prop`, with no external term
parameters. Its single universe parameter `u` is arbitrary and is
shared by the two fields `K` and `L`, as in the original; it is not
restricted to zero. All six source term binders occur inside the
defining universal quantifier, in the following order:

| Binders | Kind | Meaning |
| --- | --- | --- |
| `K`, `L` | explicit, each `Type u` | Base field and extension field |
| `[Field K]`, `[Field L]` | instance-implicit | The two field structures |
| `[Algebra K L]` | instance-implicit | The specified algebra structure |
| `x : Lˣ` | explicit | An arbitrary unit of the extension field |

The conclusion is an equation in `NormQuotient K L`. Its left side
first sends `x` to the base-field unit `normUnits K L x : Kˣ` and then
takes the class `normClass K L (normUnits K L x)`. Its right side `1`
is the identity of the published group structure
`normQuotientCommGroup K L` on the quotient. The map runs in the
original direction, from extension units `Lˣ` to base units `Kˣ`;
the proposition does not concern classes of arbitrary base-field
units. A client applies it as `H K L x` to obtain the equation for
given fields, algebra structure and unit.

The statement assumes no finite-dimensionality, finite-module
condition, separability, Galois property, local-field structure,
valuation, topology or surjectivity hypothesis. No additional
hypothesis or instance is introduced here. Every binder is used, so
no linter option is needed.

## Actual unit norm, norm subgroup and quotient

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U016.Proofs`.
It preserves the published `M093.016.END` boundary and supplies the
following unchanged definitions through its dependencies:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

Thus `normUnits K L : Lˣ →* Kˣ` is the actual unit norm, the subgroup
is its actual range in `Kˣ`, `NormQuotient K L` is the named quotient
of `Kˣ` by that range, and `normClass K L` is the canonical quotient
homomorphism, defined as `QuotientGroup.mk' (localNormSubgroup K L)`
after exposing the concrete quotient. The target of `normClass K L`
carries the published `normQuotientCommGroup` structure. The
proposition uses these named maps and this named quotient; it does
not substitute an arbitrary subgroup, quotient or projection.
Informally, it says that `normClass K L` sends every element of the
subgroup `localNormSubgroup K L` to the identity.

The norm is Mathlib's unrestricted `Algebra.norm K`, defined as the
determinant of multiplication in the approved
`Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62.
`Algebra.norm_eq_one_of_not_module_finite`, lines 76–79, states that
this norm is constantly `1` when `L` is not a finite `K`-module.
In that case `normUnits K L x = 1` for every unit `x`, the unit-norm
range is the trivial subgroup, and the proposition's equation reads
`normClass K L 1 = 1`. This case remains within the proposition's
scope.

## Original passage and adaptation

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
lines 171–174](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L171-L174):
the docstring is at 171, the theorem name and its telescope at 172,
the equation at 173, and the proof at 174.
The original reads:

```lean
/-- The quotient class of any extension-unit norm is the identity norm class. -/
theorem mk_normUnits_eq_one (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ) :
    normClass K L (normUnits K L x) = 1 := by
```

The whole source file has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The complete file was read, including the underlying norm-quotient
vocabulary at 26–54, the file's `universe u v` declaration at 24, and
the preceding induction principle at 160–169. The unit norm
`normUnits` itself comes from the source file
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, lines 32–34
(SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`),
already published as NYLL unit M092.002.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.mk_normUnits_eq_one` (theorem) | `Langlands.NYLL.LocalFieldTheory.MkNormUnitsEqOneStatement` |
| `LocalFieldTheory.normUnits` | `Langlands.NYLL.LocalFieldTheory.normUnits` |
| `LocalFieldTheory.localNormSubgroup` | `Langlands.NYLL.LocalFieldTheory.localNormSubgroup` |
| `LocalFieldTheory.NormQuotient` | `Langlands.NYLL.LocalFieldTheory.NormQuotient` |
| `LocalFieldTheory.normQuotientCommGroup` | `Langlands.NYLL.LocalFieldTheory.normQuotientCommGroup` |
| `LocalFieldTheory.normClass` | `Langlands.NYLL.LocalFieldTheory.normClass` |

Only the first row introduces a declaration in this module. The
original theorem's entire telescope moves inside a closed `Prop`
definition, retaining its order, binder kinds, binder names, shared
universe and equation. The namespace gains `Langlands.NYLL`. The
original docstring is retained. The source imports become the single
published U016 Proofs import. The source proof, the noncomputable
section and all other declarations are omitted; the unused source
universe `v` is not declared. A proposition definition needs no
noncomputable section. The partition records no patch10 change to
this original module.

The original is retained in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source-ID errata locations in the workspace, project and current
Library were checked; no applicable erratum was found.

Fresh TaskHub searches and exact-name searches of the workspace,
current Library, staging and shared drafts found no competing
statement or proof port. The generic Mathlib fact is
`QuotientGroup.eq_one_iff` in the approved
`Mathlib/GroupTheory/QuotientGroup/Defs.lean`, lines 119–122, stated
for an arbitrary quotient `G ⧸ N` by a normal subgroup and its
coercion. This wrapper instead retains the source-specific named
quotient `NormQuotient K L`, class map `normClass K L` and unit norm
`normUnits K L`, so clients need not unfold the quotient
representation.

## Statement boundary and attribution

This file defines the proposition only. The theorem
`Langlands.NYLL.LocalFieldTheory.mk_normUnits_eq_one` and its proof
require a separate task after this target is independently accepted
and public. M093.018 and later source units remain separate.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
Compilation and unapplied-declaration inspection establish the
declaration shape; independent semantic review and Integrator
publication remain separate requirements.

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi
(assisted by OpenAI Codex)”, released under Apache-2.0.
The dated modification record identifies Worker 248's extraction
and changes. Worker 248 adapted this unit directly from the pinned
original and wrote this companion. No other project worker supplied
code or a reused draft. The 24 imported Library modules and their
Markdown companions remain unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included
in `repository_paths`. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching upstream. The inherited NOTICE's ValuedFieldTheory
included-source list has no NormQuotient-specific third-party entry.
Existing dependency notices and attribution are preserved.

This generic algebraic identity supplies no Artin map, Artin kernel
or surjectivity result, host quotient or evaluation adapter, or
topology theorem. Parent finite reciprocity task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` remains open.
