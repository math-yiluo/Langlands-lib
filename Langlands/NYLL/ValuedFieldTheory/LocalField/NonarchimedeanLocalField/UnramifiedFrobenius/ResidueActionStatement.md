# Residue action of the field arithmetic Frobenius: target

This module states NYLL source unit M264.010 as a closed proposition. It
exports one Prop-valued definition,
`Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_applyStatement`.
Nothing is proved here; the proof is a separate unit under the adapted source
name
`Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply`.

Mathematically, the target says: let `L/K` be a finite Galois unramified
extension of nonarchimedean local fields, with `q` elements in the residue
field `𝓀[K]`. Then the field arithmetic Frobenius `Frob ∈ Gal(L/K)` acts on the
residue field `𝓀[L]` by `x ↦ x ^ q`. This is the defining property of
arithmetic Frobenius, stated through the residue action of integral elements.
The M269 statement `finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow`
is proved from it.

## The proposition

```lean
def galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_applyStatement :
    Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : 𝓀[L]),
    galoisGroupResidueAlgEquivOfIsIntegralClosure K L
        (arithmeticFrobeniusOfUnramifiedValuation K L) x =
      x ^ Nat.card 𝓀[K]
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
| `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]` | the valuation of `L` extends that of `K`; this gives the residue algebra `𝓀[K] → 𝓀[L]` |
| `[IsIntegralClosure 𝒪[L] 𝒪[K] L]` | `𝒪[L]` is the integral closure of `𝒪[K]` in `L` |
| `[Module.Finite 𝒪[K] 𝒪[L]]` | `𝒪[L]` is a finite `𝒪[K]`-module |
| `[IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]` | `𝓂[L]` has ramification index one over `𝒪[K]` |
| `x : 𝓀[L]` | a residue class of `L` |

The conclusion compares two elements of `𝓀[L]`. On the left,
`galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ` is the residue
automorphism induced by `σ`, applied at `σ = arithmeticFrobeniusOfUnramifiedValuation K L`
and then evaluated at `x`. On the right, `Nat.card 𝓀[K]` is the number of
elements of the finite residue field of `K`.

### Published declarations used

- `Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure`
  (M160.005, [residue algebra definitions](../ResidueGalois/AlgebraDefinitions.md)):
  the map `Gal(L/K) → (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])` sending `σ` to the residue
  automorphism induced by the restriction of `σ` to `𝒪[L]`.
- `Langlands.NYLL.LocalFieldTheory.arithmeticFrobeniusOfUnramifiedValuation`
  (M264.007, [field arithmetic Frobenius](FieldDefinitions.md)): the element
  of `Gal(L/K)` whose residue automorphism, under the isomorphism M161.036, is
  the residue arithmetic Frobenius M264.001.
- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`
  (M161.001, [the class](../FiniteUnramified/Definitions.md)), at universes
  `u u`.

`𝒪[F]`, `𝓂[F]` and `𝓀[F]` are Mathlib's scoped `ValuativeRel` notation for
the integer ring of the valuation of `F`, its maximal ideal and its residue
field.

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings. Inspection of the declaration reported kind
`definition`, level parameters `[u]`, `statement_returns_prop: true`, and only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Imports and scope

The only import is the published module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius.FieldDefinitions`.
It supplies `arithmeticFrobeniusOfUnramifiedValuation` and, through its
imports, `galoisGroupResidueAlgEquivOfIsIntegralClosure`, the class
`IsUnramifiedValuedExtension`, Mathlib's `IsNonarchimedeanLocalField`,
`IsGalois`, `IsIntegralClosure`, `Nat.card` and the residue-field notation.

Only M264.010 is stated. The source lemmas it is proved from in the source
(M264.002, M264.008, M264.009 and M161.037) are not stated here; the separate
proof unit need not use them.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean#L175-L190)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `7839a2b17c7afc0b94c113a3b528b252dd05954e7452d282ff173d615b923104`, the
value recorded for M264 in the
[public declaration partition](../../../../../../notes/reuse/nyll-public-port/m263-m269.md#m264).

| Partition unit | Original theorem in `LocalFieldTheory` | Original lines | Adapted target in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- | --- |
| M264.010 | `galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply` | 175–190 | `galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_applyStatement` |

Lines 175–176 are the doc comment, line 177 the theorem name, lines 178–188
the parameters and the conclusion, and lines 189–190 the source proof. The
source module opens namespace `LocalFieldTheory` (line 22), declares
`universe u` (line 28) and opens `ValuativeRel` notation (line 30); the adapted
module does the same in `Langlands.NYLL.LocalFieldTheory`.

Worker 3 made these changes on 13 November 2026:

- added the `Langlands.NYLL` namespace prefix. The residue action, the field
  arithmetic Frobenius and the unramified class are the published prefixed
  declarations of the same names. The source spells the class
  `LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`;
  inside `Langlands.NYLL.LocalFieldTheory` the shorter spelling resolves to
  the published class;
- packaged the theorem type as the closed proposition above. The source's
  explicit and instance parameters become `∀`-binders, in the same order and
  of the same kinds (explicit for `K L` and `x`, instance-implicit for the
  rest);
- omitted the source proof;
- replaced the source imports by the published module above.

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
