# Identity norm classes

This module defines the closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqOneIffStatement`.
It states that, for every algebra `L` over a field `K`, a unit of `K`
has the identity class in the published norm quotient
`Langlands.NYLL.LocalFieldTheory.NormQuotient K L` exactly when it is
the norm of some unit of `L`.
This is the statement phase of M093.018 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Defining this proposition does not prove it.

## Complete closed interface

Inside `Langlands.NYLL.LocalFieldTheory`, the definition is:

```lean
def NormClassEqOneIffStatement.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ),
    normClass K L x = 1 ↔ ∃ y : Lˣ, normUnits K L y = x
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
| `x : Kˣ` | explicit | An arbitrary unit of the base field |

The conclusion is an equivalence, and both directions are part of the
proposition. Its left side is the equation `normClass K L x = 1` in
`NormQuotient K L`, where `1` is the identity of the published group
structure `normQuotientCommGroup K L` on the quotient. Its right side
is the existential statement `∃ y : Lˣ, normUnits K L y = x`. The
witness `y` is a unit of the extension field `L`, and the equation
`normUnits K L y = x` is an equation in `Kˣ`, written in this order.
The norm runs in the original direction, from extension units `Lˣ`
to base units `Kˣ`. A client applies the proposition as `H K L x`.
Then `(H K L x).1` turns an identity class into a norm witness, and
`(H K L x).2` turns a norm witness into an identity class.

The statement assumes no finite-dimensionality, finite-module
condition, separability, Galois property, local-field structure,
valuation, topology or surjectivity hypothesis. No additional
hypothesis or instance is introduced here. Every binder is used, so
no linter option is needed.

## Actual unit norm, norm subgroup and quotient

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U017.Proofs`.
It preserves the published `M093.017.END` boundary and supplies the
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

By Mathlib's `MonoidHom.mem_range`, in the approved
`Mathlib/Algebra/Group/Subgroup/Ker.lean`, lines 77–79, the right side
`∃ y : Lˣ, normUnits K L y = x` is definitionally the membership
`x ∈ localNormSubgroup K L`. Informally, the proposition therefore
says that the kernel of `normClass K L` is exactly the subgroup
`localNormSubgroup K L`. Its reverse direction also follows from the
published statement M093.017,
`Langlands.NYLL.LocalFieldTheory.MkNormUnitsEqOneStatement`, applied
to the witness `y`; the forward direction is new in M093.018.

The norm is Mathlib's unrestricted `Algebra.norm K`, defined as the
determinant of multiplication in the approved
`Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62.
`Algebra.norm_eq_one_of_not_module_finite`, lines 76–79, states that
this norm is constantly `1` when `L` is not a finite `K`-module.
In that case `normUnits K L y = 1` for every unit `y`, so the right
side holds exactly when `x = 1`. This case remains within the
proposition's scope.

## Original passage and adaptation

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
lines 176–181](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L176-L181):
the docstring is at 176, the theorem name and its telescope at
177–178, the equivalence at 179, and the proof at 180–181.
The original statement reads:

```lean
/-- A base-field unit has trivial norm class exactly when it lies in the local norm subgroup. -/
theorem normClass_eq_one_iff (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x : Kˣ) :
    normClass K L x = 1 ↔ ∃ y : Lˣ, normUnits K L y = x := by
```

The whole source file has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The complete file was read, including the underlying norm-quotient
vocabulary at 26–54, the file's `universe u v` declaration at 24, and
the preceding theorem `mk_normUnits_eq_one` at 171–174. The unit norm
`normUnits` itself comes from the source file
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, lines 32–34
(SHA-256
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`),
already published as NYLL unit M092.002.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normClass_eq_one_iff` (theorem) | `Langlands.NYLL.LocalFieldTheory.NormClassEqOneIffStatement` |
| `LocalFieldTheory.normUnits` | `Langlands.NYLL.LocalFieldTheory.normUnits` |
| `LocalFieldTheory.localNormSubgroup` | `Langlands.NYLL.LocalFieldTheory.localNormSubgroup` |
| `LocalFieldTheory.NormQuotient` | `Langlands.NYLL.LocalFieldTheory.NormQuotient` |
| `LocalFieldTheory.normQuotientCommGroup` | `Langlands.NYLL.LocalFieldTheory.normQuotientCommGroup` |
| `LocalFieldTheory.normClass` | `Langlands.NYLL.LocalFieldTheory.normClass` |

Only the first row introduces a declaration in this module. The
original theorem's entire telescope moves inside a closed `Prop`
definition, retaining its order, binder kinds, binder names, shared
universe and equivalence, including the witness name `y`. The
namespace gains `Langlands.NYLL`. The original docstring is retained.
The source imports become the single published U017 Proofs import.
The source proof, the noncomputable section and all other
declarations are omitted; the unused source universe `v` is not
declared. A proposition definition needs no noncomputable section.
The partition records no patch10 change to this original module.

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
for an arbitrary quotient `G ⧸ N` by a normal subgroup, its coercion
and subgroup membership. This wrapper instead retains the
source-specific named quotient `NormQuotient K L`, class map
`normClass K L` and unit norm `normUnits K L`, and it states the
membership as an explicit existential norm witness, so clients need
not unfold the quotient representation or the range.

## Statement boundary and attribution

This file defines the proposition only. The theorem
`Langlands.NYLL.LocalFieldTheory.normClass_eq_one_iff` and its proof
require a separate task after this target is independently accepted
and public. M093.019 and later source units, auxiliary instances and
host adapters remain separate.

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
code or a reused draft. The imported Library modules and their
Markdown companions remain unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included
in `repository_paths`. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching upstream. The inherited NOTICE's ValuedFieldTheory
included-source list has no NormQuotient-specific third-party entry.
Existing dependency notices and attribution are preserved.

This generic quotient criterion supplies no Artin map, Artin kernel
or surjectivity result, host quotient or evaluation adapter, or
topology theorem. Parent finite reciprocity task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` remains open.
