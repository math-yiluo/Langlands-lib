# Unique valuation extension for general discrete valuation fields

This module defines
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension`.
It extracts the single predicate M304.001 from Naganori Yamaguchi's
[`RealLowerGroups.lean`, lines 40–53](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L40-L53),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The complete original file has SHA-256
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.

## Full telescope and body

The existing bundle `DVF` below is
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF`, imported from
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`.
Each bundle stores its value group, its ordered group structure, its chosen
valuation and its rank-one discreteness proof.
With that namespace opened, the full parameter context and definition are:

```lean
universe u v w x y
variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

def HasUniqueValuationExtension (base : DVF.{u, v} K)
    (target : DVF.{w, x} L) : Prop :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
      target.valuation.IsEquiv v'
```

The carrier parameters `K` and `L` are implicit. The supplied field structures
and the supplied `Algebra K L` are instance parameters. The two chosen bundles
`base` and `target` are explicit arguments. The result is a parameterized
`Prop`, with no target-extension hypothesis in its telescope.

All five universe levels are independent:

| Level | Role |
| --- | --- |
| `u` | Base field carrier `K`. |
| `v` | `base.ValueGroup`. |
| `w` | Target field carrier `L`. |
| `x` | `target.ValueGroup`. |
| `y` | Comparison value group `Gamma'`. |

For each choice of these levels, the predicate quantifies over all
`Gamma' : Type y` and all supplied
`LinearOrderedCommGroupWithZero Gamma'` structures, then over an explicit
valuation `v' : Valuation L Gamma'`, and then over the instance argument
`[base.valuation.HasExtension v']`. The conclusion has the chosen target
valuation first: `target.valuation.IsEquiv v'`. This quantifier and
instance-binder order is the source order. In particular, `y` is an independent
universe parameter of the predicate; it is neither fixed to `x` nor restricted
to `0`.

## Extension and equivalence conventions

The second import is `Mathlib.RingTheory.Valuation.Extension`. Its existing
`Valuation.HasExtension` class uses the actual `algebraMap K L` belonging to
the supplied algebra structure. The hypothesis
`base.valuation.HasExtension v'` has the single field

```lean
base.valuation.IsEquiv (v'.comap (algebraMap K L))
```

Thus the restriction agrees up to valuation equivalence; equality of values
or of value groups is not required. Mathlib's `Valuation.IsEquiv v₁ v₂`
means precisely
`∀ a b, v₁ a ≤ v₁ b ↔ v₂ a ≤ v₂ b`. Consequently the conclusion here is

```lean
∀ a b : L, target.valuation a ≤ target.valuation b ↔ v' a ≤ v' b
```

The predicate asserts uniqueness up to this equivalence among comparison
valuations satisfying the extension condition. It neither constructs such
a valuation nor assumes or asserts
`base.valuation.HasExtension target.valuation`. If the comparison valuations
at the chosen universe have no extension instances, its universally quantified
implication is vacuous. Existence and compatibility of the chosen target are
separate mathematical conditions.

No finite-dimensionality, separability, completeness, Henselianity,
local-field or Galois condition is present. The comparison valuation is not
required to be discrete. The module introduces no theorem or instance and
leaves the existing chosen-local-field uniqueness statement unchanged.
Automorphism compatibility, valuation-ring preservation and ramification
groups are separate units.

## Source correspondence and modifications

| Original at the pinned commit | Adaptation |
| --- | --- |
| `RamificationTheory.DiscreteValuationField`, line 35, and `DVF`, line 39 | Prefix the namespace with `Langlands.NYLL`; retain the `DVF` namespace. |
| Open `ValuationTheory.DiscreteValuationField`, line 37 | Open the published `Langlands.NYLL.ValuationTheory.DiscreteValuationField` bundle namespace. |
| Universes, line 33, and carrier/instance context, line 41 | Preserve `u v w x y`, both implicit carriers, both supplied fields and the supplied algebra. |
| `RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension`, lines 48–52 | `Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension`, with the same explicit bundle arguments, quantifiers and body. |

Worker 1199 isolated this predicate and wrote its companion explanation on
1 November 2026. Worker 106 supplied the exact formulation and the focused
source boundary in the task. The adaptation replaces the upstream DVF import
with its published module, omits the unused real-number and Galois imports,
omits the unused `noncomputable section` and `Pointwise` scope, and clarifies
the definition's documentation. The predicate itself has no mathematical
modification. The source partition records no patch10 change for M304;
no compatibility patch was needed for this extraction.

The source snapshot is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original author and copyright header is retained: copyright 2026 Naganori
Yamaguchi, all rights reserved; authors Naganori Yamaguchi (assisted by OpenAI
Codex). The source is Apache-2.0. Existing verbatim copies of its
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in the Library.
The original NOTICE has no source-specific entry for `RealLowerGroups.lean`.
No applicable errata were found in the project or published errata locations.
