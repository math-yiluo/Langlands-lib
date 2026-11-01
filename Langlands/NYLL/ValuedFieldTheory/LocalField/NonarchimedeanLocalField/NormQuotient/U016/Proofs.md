# Induction on norm-quotient classes

This module proves the protected theorem
`Langlands.NYLL.LocalFieldTheory.NormQuotient.inductionOn`.
Its complete unapplied type is the already published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientInductionOnStatement.{u}`.
This is the proof phase of M093.016 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).

## Closed target and binders

The target internally quantifies over exactly this telescope and conclusion:

```lean
∀ {K L : Type u} [Field K] [Field L] [Algebra K L]
  {motive : NormQuotient K L → Prop} (q : NormQuotient K L)
  (h : ∀ x : Kˣ, motive (normClass K L x)), motive q
```

All eight term binders are inside the closed proposition, in this order:

| Binders | Kind | Meaning |
| --- | --- | --- |
| `K`, `L` | implicit, each `Type u` | Base field and algebra field |
| `[Field K]`, `[Field L]` | instance-implicit | The two field structures |
| `[Algebra K L]` | instance-implicit | The specified algebra structure |
| `motive : NormQuotient K L → Prop` | implicit | The property of norm-quotient classes |
| `q : NormQuotient K L` | explicit | The arbitrary class in the conclusion |
| `h : ∀ x : Kˣ, motive (normClass K L x)` | explicit | The property for the class of every unit |

The conclusion is `motive q` for the same arbitrary class `q`, and `h`
quantifies over every unit `x : Kˣ`. The single universe parameter `u` is
arbitrary and is shared by `K` and `L`; it is not restricted to zero. The
motive is valued in `Prop`, so the theorem eliminates into propositions
only. The theorem has no external term parameters and adds no hypothesis:
no finite-dimensionality, finite-module condition, separability, Galois
property, valuation, topology or surjectivity assumption.

The sole direct import is the published U016 Statements module. Through
its U015 Proofs import it keeps the published `M093.015.END` boundary and
the unchanged named constructions:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
normClass K L : Kˣ →* NormQuotient K L
```

So the subgroup is the actual range of the unit norm `Lˣ →* Kˣ`,
`NormQuotient K L` is the named quotient of `Kˣ` by that range, and
`normClass K L x` is the canonical class of `x`, defined as
`QuotientGroup.mk' (localNormSubgroup K L)`. The norm is Mathlib's
unrestricted `Algebra.norm K`. By `Algebra.norm_eq_one_of_not_module_finite`
it is constantly `1` when `L` is not a finite `K`-module. The norm image is
then trivial, and the theorem still covers that case.

## Implemented proof

The proof introduces the target's eight binders, naming the three
instances anonymously, then follows the original proof at lines 166–169
without changing its steps:

```lean
intro K L _ _ _ motive q h
change motive (show Kˣ ⧸ localNormSubgroup K L from q)
refine QuotientGroup.induction_on q ?_
intro x
exact h x
```

The `change` exposes the concrete quotient: it views `q` as an element of
`Kˣ ⧸ localNormSubgroup K L`, which is definitionally `NormQuotient K L`.
Mathlib's `QuotientGroup.induction_on`, in the approved
`Mathlib/GroupTheory/Coset/Defs.lean` at lines 171–173, then reduces the
goal to `motive (QuotientGroup.mk x)` for an arbitrary representative
`x : Kˣ`. That goal is definitionally `motive (normClass K L x)`, because
`normClass K L x` unfolds to `QuotientGroup.mk' (localNormSubgroup K L) x`,
which is `QuotientGroup.mk x`. The supplied hypothesis `h x` therefore
closes it.

The proof uses only the quotient's own induction principle. It introduces
no choice construction and does not use `normQuotientConcreteEquiv`.
The published statement itself already depends on `propext`,
`Classical.choice` and `Quot.sound` through its imported definitions; the
proof adds no further axiom.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`,
lines 160–169](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L160-L169):
the docstring at 160–161, the protected theorem with its telescope and
conclusion at 162–165, and the proof at 166–169. The complete original
file was read and its SHA-256 verified as
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `LocalFieldTheory.NormQuotient.inductionOn` (protected theorem) | `NormQuotient.inductionOn` (protected theorem), proving the closed published target |
| Same theorem's statement | Existing `NormQuotientInductionOnStatement` |
| `LocalFieldTheory.NormQuotient` | Existing `NormQuotient` |
| `LocalFieldTheory.normClass` | Existing `normClass` |
| `LocalFieldTheory.localNormSubgroup` | Existing `localNormSubgroup` |
| `LocalFieldTheory.normUnits` | Existing `normUnits` |

Only the first row introduces a declaration here. Modifications by
Worker 1160 on 31 October 2026 are: add the `Langlands.NYLL` namespace
prefix; replace the source imports with the sole U016 Statements import;
give the theorem the closed published proposition as its type and
introduce its internal binders; omit the noncomputable section, the
unused universe `v` and all other source declarations. The `protected`
modifier, the original theorem name, its docstring and the proof steps
are kept. The partition records no patch10 change to this original
module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable source-ID erratum exists in the workspace, project or
current Library. Searches of the workspace, current Library, staging and
shared drafts found no earlier proof port; the only other copies of the
original passage are old upstream audit drafts, which were not reused.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; the original proof needed no
change for the approved environment. A development check compiled the
module with no diagnostics. It found a theorem with level parameter `u`
whose unapplied type is the constant
`NormQuotientInductionOnStatement.{u}`, using only `propext`,
`Classical.choice` and `Quot.sound`. This check does not establish
independent semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 1160 adapted this proof directly from
the pinned original and wrote this companion. No other project worker
supplied code or a reused draft for this proof. Worker 248's statement
and the imported constructions are used unchanged; all imported Library
modules and their paired Markdown remain frozen.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included in
`repository_paths` and are byte-identical to the retained originals.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The inherited NOTICE has no NormQuotient-specific third-party entry, and
all inherited dependency notices remain intact. No Mathlib code is
copied into this file.

This generic algebraic quotient-induction proof supplies no Artin map,
Artin kernel or surjectivity result, host quotient or evaluation adapter,
or topology theorem. M093.017 and later source units remain separate,
and parent finite reciprocity task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` remains open.
