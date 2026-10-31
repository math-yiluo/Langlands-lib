# Induction on norm-quotient classes

This module defines the closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientInductionOnStatement`.
It packages the elimination principle for the published norm quotient
`Langlands.NYLL.LocalFieldTheory.NormQuotient`: a property of quotient
classes holds for an arbitrary class once it holds for the canonical
class of every base-field unit.
This is the statement phase of M093.016 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Defining this proposition does not prove it.

## Complete closed interface

Inside `Langlands.NYLL.LocalFieldTheory`, the definition is:

```lean
def NormQuotientInductionOnStatement.{u} : Prop :=
  ∀ {K L : Type u} [Field K] [Field L] [Algebra K L]
    {motive : NormQuotient K L → Prop} (q : NormQuotient K L)
    (h : ∀ x : Kˣ, motive (normClass K L x)), motive q
```

The unapplied declaration has type `Prop`, with no external term
parameters. Its single universe parameter `u` is arbitrary and is
shared by the two fields `K` and `L`, as in the original; it is not
restricted to zero. All eight source term binders occur inside the
defining universal quantifier, in the following order:

| Binders | Kind | Meaning |
| --- | --- | --- |
| `K`, `L` | implicit, each `Type u` | Base field and algebra field |
| `[Field K]`, `[Field L]` | instance-implicit | The two field structures |
| `[Algebra K L]` | instance-implicit | The specified algebra structure |
| `motive : NormQuotient K L → Prop` | implicit | The property of norm-quotient classes |
| `q : NormQuotient K L` | explicit | The arbitrary class in the conclusion |
| `h : ∀ x : Kˣ, motive (normClass K L x)` | explicit | The property for the class of every unit |

The conclusion is `motive q` for the same class `q`. The representative
`x` is universally quantified over all of `Kˣ` inside `h`. The motive
is valued in `Prop`, as in the source; it is not generalized to
`Sort`, so the proposition gives elimination into propositions only.

The statement assumes no finite-dimensionality, finite-module
condition, separability, Galois property, local-field structure,
valuation, topology or surjectivity hypothesis. No additional
hypothesis or instance is introduced here.

The hypothesis `h` is never mentioned in the conclusion, so Lean's
unused-variables linter would warn about it. The Lean file keeps the
source name `h` and turns that linter off for this one declaration with
`set_option linter.unusedVariables false in`. The option affects only
linting of this declaration, not its meaning.

## Actual norm quotient and canonical representatives

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U015.Proofs`.
It preserves the published `M093.015.END` boundary and supplies the
following unchanged definitions through its dependencies:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

Thus the subgroup is the actual range of the unit norm `Lˣ →* Kˣ`,
`NormQuotient K L` is the named quotient of `Kˣ` by that range, and
`normClass K L x` is the canonical quotient class of `x`, defined as
`QuotientGroup.mk' (localNormSubgroup K L)` after exposing the
concrete quotient. In `h`, `normClass K L` is applied as a monoid
homomorphism whose target carries the published
`normQuotientCommGroup` structure. The proposition quantifies over
motives on this named quotient type and uses this named class map;
it does not substitute an arbitrary quotient or projection.

The norm is Mathlib's unrestricted `Algebra.norm K`, defined as the
determinant of multiplication in the approved
`Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62.
`Algebra.norm_eq_one_of_not_module_finite`, lines 76–79, states that
this norm is constantly `1` when `L` is not a finite `K`-module.
In that case the unit-norm range is the trivial subgroup and
`NormQuotient K L` is `Kˣ` modulo the trivial subgroup. This case
remains within the proposition's scope.

## Original passage and adaptation

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
lines 160–169](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L160-L169):
the docstring is at 160–161, the protected theorem, its telescope
and its conclusion at 162–165, and the proof at 166–169.
The original reads:

```lean
protected theorem NormQuotient.inductionOn {K L : Type u} [Field K] [Field L]
    [Algebra K L] {motive : NormQuotient K L → Prop}
    (q : NormQuotient K L)
    (h : ∀ x : Kˣ, motive (normClass K L x)) : motive q := by
```

The whole source file has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The complete file was read, including the underlying norm
vocabulary at 26–54, the file's `universe u v` declaration at 24, and
the preceding first-isomorphism units at 137–158.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.NormQuotient.inductionOn` (protected theorem) | `Langlands.NYLL.LocalFieldTheory.NormQuotientInductionOnStatement` |
| `LocalFieldTheory.NormQuotient` | `Langlands.NYLL.LocalFieldTheory.NormQuotient` |
| `LocalFieldTheory.normClass` | `Langlands.NYLL.LocalFieldTheory.normClass` |
| `LocalFieldTheory.normQuotientCommGroup` | `Langlands.NYLL.LocalFieldTheory.normQuotientCommGroup` |
| `LocalFieldTheory.localNormSubgroup` | `Langlands.NYLL.LocalFieldTheory.localNormSubgroup` |
| `LocalFieldTheory.normUnits` | `Langlands.NYLL.LocalFieldTheory.normUnits` |

Only the first row introduces a declaration in this module. The
original protected theorem's entire telescope moves inside a closed
`Prop` definition, retaining its order, binder kinds, binder names,
shared universe, `Prop`-valued motive and conclusion `motive q`. The
namespace gains `Langlands.NYLL`. The original docstring is retained.
The source imports become the single published U015 Proofs import.
The source proof, the `protected` modifier, the noncomputable section
and all other declarations are omitted; the unused source universe `v`
is not declared. A proposition definition needs no noncomputable
section. The local linter option described above is the only other
addition. The partition records no patch10 change to this original
module.

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
statement or proof port. The generic Mathlib principle is
`QuotientGroup.induction_on` in the approved
`Mathlib/GroupTheory/Coset/Defs.lean`, lines 171–173, stated for an
arbitrary quotient `α ⧸ s` and its coercion `QuotientGroup.mk`.
This wrapper instead retains the source-specific named quotient
`NormQuotient K L` and class map `normClass K L`, so clients need not
unfold the quotient representation.

## Statement boundary and attribution

This file defines the proposition only. The protected theorem
`Langlands.NYLL.LocalFieldTheory.NormQuotient.inductionOn` and its
proof require a separate task after this target is independently
accepted and public. M093.017 and later source units remain separate.

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
code or a reused draft. The 22 imported Library modules and their
Markdown companions remain unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included
in `repository_paths`. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching upstream. The inherited NOTICE's ValuedFieldTheory
included-source list has no NormQuotient-specific third-party entry.
Existing dependency notices and attribution are preserved.

This generic algebraic quotient-induction statement supplies no
Artin map, Artin kernel or surjectivity result, host quotient or
evaluation adapter, or topology theorem. Parent finite reciprocity
task `1cbd1968-d285-4b34-822c-f6b5599d1c38` remains open.
