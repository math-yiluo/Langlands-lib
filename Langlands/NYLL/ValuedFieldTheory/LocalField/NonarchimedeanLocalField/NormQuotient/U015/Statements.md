# First-isomorphism equivalence on norm classes

This module defines the closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientEquivOfSurjectiveNormClassStatement`.
It packages the representative equation for the published
`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSurjective`.
This is the statement phase of M093.015 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Defining this proposition does not prove it.

## Complete closed interface

Inside `Langlands.NYLL.LocalFieldTheory`, the definition is:

```lean
def NormQuotientEquivOfSurjectiveNormClassStatement.{u,v} : Prop :=
  ∀ {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) (x : Kˣ),
    normQuotientEquivOfSurjective f hf hker (normClass K L x) = f x
```

The unapplied declaration has type `Prop`, with no external term
parameters. Its universe parameters `u` and `v` are independent and
arbitrary. The fields `K` and `L` share universe `u`; the target group
`M` lies in universe `v`. Neither universe is restricted to zero.
All eleven source term binders occur inside the defining universal
quantifier, in the following order:

| Binders | Kind | Meaning |
| --- | --- | --- |
| `K`, `L` | implicit, each `Type u` | Base field and algebra field |
| `M` | implicit, `Type v` | Target group |
| `[Field K]`, `[Field L]` | instance-implicit | The two field structures |
| `[Algebra K L]` | instance-implicit | The specified algebra structure |
| `[Group M]` | instance-implicit | Only a group structure on the target |
| `f : Kˣ →* M` | explicit | Supplied multiplicative homomorphism |
| `hf : Function.Surjective f` | explicit | Supplied surjectivity proof |
| `hker : f.ker = localNormSubgroup K L` | explicit | Exact kernel equality in this orientation |
| `x : Kˣ` | explicit | The representative on both sides |

The statement assumes no commutativity of `M`, finite-dimensionality,
finite-module condition, separability, Galois property, local-field
structure, valuation or topology. The norm-subgroup normality needed
by the imported constructor follows from commutativity of `Kˣ`.
No additional hypothesis or instance is introduced here.

## Actual norm quotient and the representative equation

The sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U014.Definitions`.
It preserves the published `M093.014.END` boundary and supplies the
following unchanged definitions through its dependencies:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

Thus the subgroup is the actual range of the unit norm `Lˣ →* Kˣ`,
and `normClass K L x` is the canonical quotient class of `x`.
The supplied `hker` identifies `f.ker` with this specific norm image.
The published U014 constructor has type `NormQuotient K L ≃* M`.
After exposing the concrete quotient, it composes
`QuotientGroup.quotientMulEquivOfEq hker.symm` with
`QuotientGroup.quotientKerEquivOfSurjective f hf`.
The first factor transports from the quotient by the norm image to
the quotient by `f.ker`; the second is the canonical first-isomorphism
equivalence for `f`. Its inverse uses a classical choice of preimages
from the supplied surjectivity.

Both sides of the asserted equation lie in `M`. The left side
coerces this named multiplicative equivalence to a function and
evaluates it on the named norm class of `x`. The right side is
`f x` for the same representative. The proposition preserves these
named constructions rather than substituting an arbitrary equivalence.

The norm is Mathlib's unrestricted `Algebra.norm K`, defined as the
determinant of multiplication in the approved
`Mathlib/RingTheory/Norm/Defs.lean`, lines 59–62.
`Algebra.norm_eq_one_of_not_module_finite`, lines 76–79, states that
this norm is constantly `1` when `L` is not a finite `K`-module.
In that case the unit-norm range is the trivial subgroup and `hker`
requires the kernel of `f` to be trivial. This case remains within
the proposition's scope.

## Original passage and adaptation

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
lines 146–158](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L146-L158):
the docstring is at 146, the `simp` attribute at 147, the theorem
telescope and equation at 148–152, and the proof at 153–158.
The whole source file has SHA-256
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The complete file was read, including the underlying norm vocabulary
and the preceding first-isomorphism constructor at 137–144.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normQuotientEquivOfSurjective_normClass` | `Langlands.NYLL.LocalFieldTheory.NormQuotientEquivOfSurjectiveNormClassStatement` |
| `LocalFieldTheory.normQuotientEquivOfSurjective` | `Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSurjective` |
| `LocalFieldTheory.normClass` | `Langlands.NYLL.LocalFieldTheory.normClass` |
| `LocalFieldTheory.NormQuotient` | `Langlands.NYLL.LocalFieldTheory.NormQuotient` |
| `LocalFieldTheory.localNormSubgroup` | `Langlands.NYLL.LocalFieldTheory.localNormSubgroup` |
| `LocalFieldTheory.normUnits` | `Langlands.NYLL.LocalFieldTheory.normUnits` |

Only the first row introduces a declaration in this module. The
original theorem's entire telescope moves inside a closed `Prop`
definition, retaining its order, binder kinds, two universes, kernel
equality orientation and representative equation. The namespace gains
`Langlands.NYLL`. The original docstring is retained. The source
imports become the single published U014 Definitions import.
The source proof, `@[simp]` registration, noncomputable section and
all other declarations are omitted. A proposition definition needs
no noncomputable section. The partition records no patch10 change
to this original module.

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

Fresh TaskHub and exact-name Lean searches in the workspace, current
Library, staging, shared drafts and approved Mathlib found no competing
statement or proof port. Two upstream copies in the old source-audit
draft were found and were not reused. The generic Mathlib quotient
mechanisms are read at
`Mathlib/GroupTheory/QuotientGroup/Basic.lean`, lines 137–173.
This wrapper retains the source-specific named constructor and class
map interface.

## Statement boundary and attribution

This file defines the proposition only. The exact theorem
`Langlands.NYLL.LocalFieldTheory.normQuotientEquivOfSurjective_normClass`,
its proof and source simp registration require a separate task after
this target is independently accepted and public. M093.016 and later
source units remain separate.

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
The dated modification record identifies Worker 107's extraction
and changes. Worker 107 adapted this unit directly from the pinned
original and wrote this companion. No other project worker supplied
code or a reused draft. The 20 imported Library modules and their
Markdown companions remain unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included
in `repository_paths`. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching upstream. The inherited NOTICE's ValuedFieldTheory
included-source list has no NormQuotient-specific third-party entry.
Existing dependency notices and attribution are preserved.

This generic conditional algebraic statement supplies no named
Artin map, proof of its kernel or surjectivity, host quotient or
evaluation adapter, or topology theorem. Parent finite reciprocity
task `1cbd1968-d285-4b34-822c-f6b5599d1c38` remains open.
