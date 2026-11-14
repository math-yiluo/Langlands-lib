# The uniformizer-power quotient has valuation zero

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactorValuationZero`.
Its type is the already published proposition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactorValuationZeroStatement`
at the universe level `u`:

```lean
theorem uniformizerUnitFactorValuationZero :
    uniformizerUnitFactorValuationZeroStatement.{u}
```

This is the proof phase of M134.037 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m134).

## Target and binders

By its definition in the published `ValuationExactSequence.KernelStatements`
module, `uniformizerUnitFactorValuationZeroStatement.{u}` is the closed
proposition

```lean
∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ x : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1),
    valuationMap K
      (Additive.ofMul (x / ϖ ^ valuationMap K (Additive.ofMul x))) = 0
```

The binders are exactly the source theorem's, in source order:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K : Type u` | explicit | The field |
| `[Field K]` | instance | Its field structure |
| `[ValuativeRel K]` | instance | Its valuative relation, which determines `ValuativeRel.valuation K` |
| `[TopologicalSpace K]` | instance | Its topology |
| `[IsNonarchimedeanLocalField K]` | instance | Mathlib's class of nonarchimedean local fields |
| `ϖ : Kˣ` | explicit | A field unit |
| `x : Kˣ` | explicit | A field unit |
| `hϖ` | explicit | `ϖ` has normalized valuation `1`, i.e. `ϖ` is a uniformizer |

`valuationMap K : Additive Kˣ →+ Int` is the published additive homomorphism
from `ValuationExactSequence.Definitions` (M134.002), the additive form
`MonoidHom.toAdditive (valuationUnitsMulHom K)` of the multiplicative
normalized valuation `valuationUnitsMulHom K : Kˣ →* Multiplicative Int`
(M134.001). The power `ϖ ^ valuationMap K (Additive.ofMul x)` is the integer
power (`zpow`) in the group `Kˣ`, with exponent the normalized valuation of
`x`, and `/` is division in `Kˣ`. The statement says that this quotient, the
integer-unit factor of `x` in the decomposition `x = u * ϖ ^ v(x)`, has
normalized valuation zero. No hypothesis is added.

The sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.KernelStatements`
module, which supplies the target and, through
`ValuationExactSequence.Definitions`, the map `valuationMap`. No proof module
is imported.

## Implemented proof

```lean
intro K _ _ _ _ ϖ x hϖ
rw [ofMul_div, map_sub, ofMul_zpow, map_zsmul, hϖ, smul_eq_mul, mul_one, sub_self]
```

Write `n` for `valuationMap K (Additive.ofMul x) : Int`.

1. `intro K _ _ _ _ ϖ x hϖ` introduces the eight binders of the statement.
   The goal is `valuationMap K (Additive.ofMul (x / ϖ ^ n)) = 0`.
2. `ofMul_div` (Mathlib, `Mathlib/Algebra/Group/TypeTags/Basic.lean`) turns
   `Additive.ofMul (x / ϖ ^ n)` into `Additive.ofMul x - Additive.ofMul (ϖ ^ n)`,
   and `map_sub` for the additive homomorphism `valuationMap K` gives
   `n - valuationMap K (Additive.ofMul (ϖ ^ n))`.
3. `ofMul_zpow` (same Mathlib file) turns `Additive.ofMul (ϖ ^ n)` into
   `n • Additive.ofMul ϖ`, and `map_zsmul` gives
   `n • valuationMap K (Additive.ofMul ϖ)`.
4. `hϖ` replaces `valuationMap K (Additive.ofMul ϖ)` by `1`; `smul_eq_mul`
   turns `n • 1` into `n * 1`, and `mul_one` into `n`.
5. The goal is now `n - n = 0`, which `sub_self` turns into `0 = 0`, closed
   by `rw`'s final reflexivity check.

Steps 2 and 3 are exactly the statements of the source wrappers
`valuationMap_ofMul_div` (M134.021) and `valuationMap_ofMul_zpow` (M134.022)
for these arguments; the only difference is that in step 3 the source
wrapper states `n * valuationMap K (Additive.ofMul ϖ)` directly, while
Mathlib's law gives the scalar multiple, converted by `smul_eq_mul`.

The development check reports that the theorem has the single level
parameter `u` and uses only `propext`, `Classical.choice` and `Quot.sound`,
all already used by the imported definitions and Mathlib; the proof adds no
further axiom.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`,
lines 419–424](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean#L419-L424):
the theorem signature at 419–423 and the proof

```lean
  rw [valuationMap_ofMul_div, valuationMap_ofMul_zpow, hϖ, mul_one, sub_self]
```

at 424. The docstring is at lines 417–418, just before the partition's start
line. The passage lies in the `LocalFieldTheory` namespace and its
`noncomputable section`, in the inner `IsNonarchimedeanLocalField`
namespace whose `open scoped ValuativeRel WithZero` directive is kept here.
The complete original file is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`;
it was read and its SHA-256 hash verified as
`8a8515596e4388771957f2c4c484e8c86767236ab79f973fa405df2d34e02908`, the hash
recorded in the partition.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactorValuationZero` (theorem) | `uniformizerUnitFactorValuationZero` (theorem), proving the published target |
| Same theorem's statement | Existing `uniformizerUnitFactorValuationZeroStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_ofMul_div` (M134.021), used by `rw` | Not used; replaced by Mathlib's `ofMul_div` and `map_sub` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_ofMul_zpow` (M134.022), used by `rw` | Not used; replaced by Mathlib's `ofMul_zpow`, `map_zsmul` and `smul_eq_mul` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` | Existing `valuationMap` |

Only the first row introduces a declaration here. Modifications by
Worker 127 on 14 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source imports
  with the sole KernelStatements import;
- give the theorem the published closed statement as its type and introduce
  its binders with `intro K _ _ _ _ ϖ x hϖ`;
- replace the two source rewrites by `valuationMap_ofMul_div` and
  `valuationMap_ofMul_zpow`, whose proofs are not in the Library (their
  statements are published in the same KernelStatements module, but a
  statement is not a proof), by the general Mathlib laws `ofMul_div`,
  `map_sub`, `ofMul_zpow`, `map_zsmul` and `smul_eq_mul`, which hold for any
  additive homomorphism and need no valuation-specific fact; the remaining
  source rewrites `hϖ`, `mul_one` and `sub_self` are kept in source order;
- omit the source `noncomputable section`, which a theorem does not need,
  and all other source declarations.

The theorem name and docstring are kept. The partition records no patch10
change to the original module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Searches of the Library, staging and shared drafts for
`uniformizerUnitFactorValuationZero` found only the published statement and
the partition row, and no earlier proof port of this theorem.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A
development check compiled the module with no diagnostics. This check does
not establish independent semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 127 adapted this proof directly from
the pinned original and wrote this companion. No other project worker
supplied code or a reused draft for this proof. The published
`ValuationExactSequence.Definitions` and
`ValuationExactSequence.KernelStatements` modules, all other imported
Library modules and their paired Markdown are used unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain in the Library
and are byte-identical to the retained originals. Their SHA-256 hashes are
respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file; Mathlib lemmas are only used by
name.

This module proves only M134.037. It does not publish M134.021, M134.022 or
any other M134 theorem as a declaration.
