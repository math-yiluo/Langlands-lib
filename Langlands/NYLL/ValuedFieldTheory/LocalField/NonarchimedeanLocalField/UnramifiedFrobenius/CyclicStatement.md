# The Galois group of a finite unramified extension is cyclic: target

This module states NYLL source unit M264.016 as a closed proposition. It
exports one Prop-valued definition,
`Langlands.NYLL.LocalFieldTheory.isCyclic_galoisGroup_of_unramifiedValuationStatement`.
Nothing is proved here; the proof is a separate unit under the adapted source
name `Langlands.NYLL.LocalFieldTheory.isCyclic_galoisGroup_of_unramifiedValuation`.

Mathematically, the target says: the Galois group `Gal(L/K)` of a finite
Galois unramified extension `L/K` of nonarchimedean local fields is cyclic.
In the source, the M267 definition
`LocalClassFieldTheory.galoisGroupEquivAbelianizationOfUnramifiedValuation`
(M267.005, `UnramifiedNormComparison.lean` line 98) uses it.

## The proposition

```lean
def isCyclic_galoisGroup_of_unramifiedValuationStatement : Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L],
    IsCyclic Gal(L / K)
```

The level parameter `u` is the only universe; `K` and `L` share it, as in the
source. The quantified binders, in order, are exactly the parameters of the
source theorem:

| Binder | Meaning |
| --- | --- |
| `K L : Type u` | the base and extension fields |
| `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` | `K` is a nonarchimedean local field (Mathlib's class) |
| the same four for `L` | `L` is a nonarchimedean local field |
| `[Algebra K L] [FiniteDimensional K L] [IsGalois K L]` | `L/K` is a finite Galois extension |
| `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]` | the valuation of `L` extends that of `K`; this gives the integer-ring algebra `𝒪[K] → 𝒪[L]` |
| `[IsIntegralClosure 𝒪[L] 𝒪[K] L]` | `𝒪[L]` is the integral closure of `𝒪[K]` in `L` |
| `[Module.Finite 𝒪[K] 𝒪[L]]` | `𝒪[L]` is a finite `𝒪[K]`-module |
| `[IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]` | `𝓂[L]` has ramification index one over `𝒪[K]` |

The conclusion is Mathlib's `IsCyclic` for the group `Gal(L / K)`, Mathlib's
notation for `L ≃ₐ[K] L`: some element generates the group under integer
powers.

### Published declarations used

- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`
  (M161.001, [the class](../FiniteUnramified/Definitions.md)), at universes
  `u u`.

`𝒪[F]` and `𝓂[F]` are Mathlib's scoped `ValuativeRel` notation for the integer
ring of the valuation of `F` and its maximal ideal.

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings. Inspection of the declaration reported kind
`definition`, level parameters `[u]`, `statement_returns_prop: true`, and only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Imports and scope

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.Definitions`
  (published): the class `IsUnramifiedValuedExtension` and, through its
  imports, Mathlib's `IsNonarchimedeanLocalField`, `Valuation.HasExtension`,
  `IsIntegralClosure` and the integer-ring notation;
- `Mathlib.FieldTheory.Galois.Basic`: `IsGalois` and the notation `Gal(L / K)`;
- `Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic`: `IsCyclic`.

Only M264.016 is stated. The source proves it from the arithmetic Frobenius
generator (M264.006, M264.014, M264.015); those units are not stated here, and
the separate proof unit need not use them.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean#L400-L412)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `7839a2b17c7afc0b94c113a3b528b252dd05954e7452d282ff173d615b923104`, the
value recorded for M264 in the
[public declaration partition](../../../../../../notes/reuse/nyll-public-port/m263-m269.md#m264).

| Partition unit | Original theorem in `LocalFieldTheory` | Original lines | Adapted target in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- | --- |
| M264.016 | `isCyclic_galoisGroup_of_unramifiedValuation` | 400–412 | `isCyclic_galoisGroup_of_unramifiedValuationStatement` |

Line 400 is the doc comment, line 401 the theorem name, lines 402–409 the
parameters and the conclusion, and lines 410–412 the source proof. The source
module opens namespace `LocalFieldTheory` (line 22), declares `universe u`
(line 28) and opens `ValuativeRel` notation (line 30); the adapted module does
the same in `Langlands.NYLL.LocalFieldTheory`.

Worker 3 made these changes on 13 November 2026:

- added the `Langlands.NYLL` namespace prefix. The unramified class is the
  published prefixed class of the same name. The source spells it
  `LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`;
  inside `Langlands.NYLL.LocalFieldTheory` the shorter spelling resolves to
  the published class;
- packaged the theorem type as the closed proposition above. The source's
  explicit and instance parameters become `∀`-binders, in the same order and
  of the same kinds (explicit for `K L`, instance-implicit for the rest);
- omitted the source proof;
- replaced the source imports by the three modules above.

No draft from another worker was used.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The partition records no patch10 change to `UnramifiedFrobenius.lean`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
