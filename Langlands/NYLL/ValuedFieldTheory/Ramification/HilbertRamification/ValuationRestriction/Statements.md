# Valuation-ring action and normal restriction

This module defines exactly one proposition:
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_integerMap_restrictNormalStatement`,
in module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationRestriction.Statements`.
It is the statement target for M398.001, with explicit uniqueness, automorphism
and element arguments. This contribution supplies no proof of the proposition.

## Complete parameters and meaning

All six universe levels `u, v, w, x, y, z` are independent. The complete
parameter context is:

```lean
{K : Type u} {L : Type w} {M : Type y}
[Field K] [Field L] [Field M]
[Algebra K L] [Algebra K M] [Algebra L M]
[IsScalarTower K L M] [Normal K L]
{base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
{middle : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
{target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{y, z} M}
[base.valuation.HasExtension middle.valuation]
[middle.valuation.HasExtension target.valuation]
[base.valuation.HasExtension target.valuation]
(hmiddle :
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
    base middle)
(htarget :
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, y, z, z}
    base target)
(σ : Gal(M/K)) (a : middle.valuationSubring)
```

The field-carrier universes are `u, w, y`; the respective chosen value-group
universes are `v, x, z`. The comparison value-group universe in each uniqueness
predicate is the target value-group universe, respectively `x` and `z`.
The extension instances refer to the three supplied field algebras, and the
scalar-tower instance makes their inclusions compatible. Normality is required
only for `K → L`; `Gal(M/K)` denotes the actual algebra-automorphism group
`M ≃ₐ[K] M`. Neither finite-dimensionality nor an `IsGalois` instance is added.

With the published action name understood, the proposition is exactly

```lean
valuationSubringAutOfUniqueExtension
      (base := base) (target := target) htarget σ
      (algebraMap middle.valuationSubring target.valuationSubring a) =
  algebraMap middle.valuationSubring target.valuationSubring
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := middle) hmiddle (σ.restrictNormal L) a)
```

Both sides lie in the very chosen `target.valuationSubring`. The first acts
by `σ` on the image of `a`; the second acts by its normal restriction on `a`
and then includes the result. The supplied algebras, chosen valuation rings
and actual action are retained.

## Pinned source correspondence

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The selected file is
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationRestriction.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationRestriction.lean#L23-L60),
SHA-256 `1eefe68fac7f1bd51c7f232dee148b4fcd1a134d9e5ee2104bb94dd116664904`.
Its complete lines 1–70 were read.

| Pinned source location | Public adaptation |
| --- | --- |
| M398 universe declaration, line 23 | Preserve all six independent levels. |
| Namespaces and open declarations, lines 25–29 | Prefix public namespaces with `Langlands.NYLL`; use qualified published names instead of the source `ValuedExtension` open. |
| Field, algebra, scalar-tower, normality, DVF and extension context, lines 31–40 | Preserve every parameter and hypothesis. |
| Theorem command, line 45; name, line 46; signature, lines 46–60 | Replace the theorem by the one Prop-valued `def` with suffix `Statement`; retain explicit `hmiddle`, `htarget`, `σ`, `a`. |
| Unique-extension hypotheses, lines 47–52 | Reuse the published full `Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF` namespace with universe specializations `u,v,w,x,x` and `u,v,y,z,z`. |
| Action and normal restriction, lines 54–60 | Reuse the published valuation-ring action and Mathlib `AlgEquiv.restrictNormal` without changing either. |
| `integerMap middle target` at lines 56–57 | Replace both occurrences by `algebraMap middle.valuationSubring target.valuationSubring`, the exact defining body of M108. |
| Proof, lines 61–65 | Omitted: proof publication is a separate task. |

The definitional replacement uses
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Extensions.lean`, lines 65–67](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Extensions.lean#L65-L67),
SHA-256 `e8999a99fc7ff6c38bd68742b9c7779decfbb2d042f60779bd2386d7950232b5`.
Lines 1–105 were read, including its context at lines 30–38. Although that
section also declares finite-dimensionality, the `integerMap` definition
does not use it: its complete type needs only the two fields, the supplied
algebra, the chosen DVFs and their extension relation. Its body is exactly
`algebraMap base.valuationSubring target.valuationSubring`. No public copy
or wrapper of `integerMap` is introduced.

## Reuse and focused compatibility

The only direct imports are the published modules
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`
and
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAut`.
They supply the existing `DVF` and its `valuationSubring` abbreviation,
the published `HasUniqueValuationExtension` predicate, and
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension`.
Mathlib supplies `Valuation.HasExtension` and its canonical valuation-ring
algebra, `algebraMap`, `Gal`, `Normal`, `IsScalarTower` and
`AlgEquiv.restrictNormal`. All are reused by Lean name. No instances are
introduced. The source imports of all of `RamificationDepth` and
`Extensions` are replaced by these focused published dependencies.

Worker 333's private check is
`.private/drafts/m398/M398Compatibility.lean`, paired with
`.private/drafts/m398/M398Compatibility.md`. It imports this focused
statement module, copies M108's exact defining body into a private
`integerMapCopy`, and proves by `rfl` that the public target is equal to
the expression with both source `integerMap` occurrences restored through
that copy. The check retains all six independent universes and all source
hypotheses. Its purpose is definitional compatibility, not a proof of M398.
The terminal compatibility check `d1ab7627-97c8-4358-95c4-d3fb7ccadf03`
succeeded with zero errors and zero warnings in the approved environment.
It built only this statement module and the private compatibility module;
the displayed complete type retained all six independent universe parameters,
all three field algebras, the scalar tower, normality and all three extension
instances.

The focused public-target check `8d244239-7999-4add-8d89-6c0c28a4d939`
also succeeded with zero errors and zero warnings. Its inspection identified
a definition in this entry module, reported universe parameters
`[u, v, w, x, y, z]`, and returned `statement_returns_prop: true`.
These development checks establish compilation and compatibility; independent
semantic acceptance and Library publication are separate requirements.

## Attribution and modifications

Worker 333 extracted the single proposition and wrote this correspondence
on 13 November 2026. Worker 300 contributed the exact canonical-map
replacement and prior private compatibility route, which was read and
repeated in this workspace. The adaptation prefixes namespaces, narrows
imports, changes the theorem to a Prop-valued target, specifies the two
uniqueness universe specializations explicitly, replaces both maps by their
defining expressions, and omits the unused `noncomputable section`, the
source `ValuedExtension` open, and the proof. There are no other
mathematical changes.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright, Apache-2.0 license and author header are retained.
The existing verbatim [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged;
their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Neither selected source file has a source-specific NOTICE entry. No applicable
NYLL errata were found in the workspace, project or published errata notes.
The environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
