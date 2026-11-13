# Arithmetic Frobenius of a finite unramified extension

This module adapts NYLL source unit M264.007. It exports one data definition,
`Langlands.NYLL.LocalFieldTheory.arithmeticFrobeniusOfUnramifiedValuation`:
the arithmetic Frobenius element of `Gal(L/K)` for a finite Galois unramified
extension `L/K` of nonarchimedean local fields. It is the unique automorphism
whose action on the residue field `𝓀[L]` is `x ↦ x ^ q`, where `q` is the
number of elements of `𝓀[K]`. The local Artin map statements of M269 express
the reciprocity map of an unramified extension through this element.

## Interface and meaning

```lean
def arithmeticFrobeniusOfUnramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L / K)
```

The level parameter `u` is the only universe; `K` and `L` share it, as in the
source. The parameters, in order, are exactly those of the source definition:

| Parameter | Meaning |
| --- | --- |
| `K L : Type u` | the base and extension fields |
| `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` | `K` is a nonarchimedean local field (Mathlib's class) |
| the same four for `L` | `L` is a nonarchimedean local field |
| `[Algebra K L] [FiniteDimensional K L] [IsGalois K L]` | `L/K` is a finite Galois extension |
| `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]` | the valuation of `L` extends that of `K` |
| `[IsIntegralClosure 𝒪[L] 𝒪[K] L]` | `𝒪[L]` is the integral closure of `𝒪[K]` in `L` |
| `[Module.Finite 𝒪[K] 𝒪[L]]` | `𝒪[L]` is a finite `𝒪[K]`-module |
| `[IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]` | the published class (M161.001): `𝓂[L]` has ramification index one over `𝒪[K]` |

`𝒪[F]`, `𝓂[F]` and `𝓀[F]` are Mathlib's scoped `ValuativeRel` notation for
the integer ring of the valuation of `F`, its maximal ideal and its residue
field. `Gal(L / K)` is `L ≃ₐ[K] L`. The two integer-ring hypotheses are
Prop-valued, so the value does not depend on which proofs of them are
supplied; the published theorem
`Langlands.NYLL.LocalFieldTheory.localCompleteDVF_integerRing_properties`
proves both for finite separable extensions of nonarchimedean local fields.
No instance is declared.

## Construction

The complete body is the source body:

```lean
  (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).symm
    (residueExtensionArithmeticFrobeniusOfValuationExtension K L)
```

- `residueExtensionArithmeticFrobeniusOfValuationExtension K L` is the
  published residue arithmetic Frobenius (M264.001, in
  [the residue definitions](ResidueDefinitions.md)): the
  `𝓀[K]`-algebra automorphism `x ↦ x ^ Fintype.card 𝓀[K]` of `𝓀[L]`.
- `galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L`
  is the published group isomorphism `Gal(L/K) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])`
  (M161.036, in
  [the isomorphism definition](../FiniteUnramified/ResidueEquivDefinitions.md)),
  whose forward map sends `σ` to its induced residue automorphism.
- `.symm` is the inverse isomorphism. So the definition is the unique
  `σ ∈ Gal(L/K)` whose residue automorphism is the residue arithmetic
  Frobenius.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings.

## Imports and scope

The two imports are the published modules that define the ingredients:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueEquivDefinitions`,
  for `galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure`
  and, through its imports, the class `IsUnramifiedValuedExtension`,
  Mathlib's `IsNonarchimedeanLocalField`, `IsGalois`, `IsIntegralClosure` and
  the residue-field notation;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius.ResidueDefinitions`,
  for `residueExtensionArithmeticFrobeniusOfValuationExtension`.

The source imports (`Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`,
`Mathlib.SetTheory.Cardinal.Finite`, `Mathlib.FieldTheory.Galois.Basic`,
`Mathlib.FieldTheory.Finite.Extension`, the NYLL module `FiniteUnramified` and
the NYLL Hensel lemma module) serve the rest of the source module. The
source's `open _root_.LocalFieldTheory.IsNonarchimedeanLocalField` is omitted;
this definition does not use it.

Only M264.007 is adapted. The source theorems M264.008–M264.010 about its
residue action, and the rest of the source module, are not ported here.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean#L126-L139)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `7839a2b17c7afc0b94c113a3b528b252dd05954e7452d282ff173d615b923104`, the
value recorded for M264 in the
[public declaration partition](../../../../../../notes/reuse/nyll-public-port/m263-m269.md#m264).

| Partition unit | Original definition in `LocalFieldTheory` | Original lines | Adapted definition in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- | --- |
| M264.007 | `arithmeticFrobeniusOfUnramifiedValuation` | 126–139 | `arithmeticFrobeniusOfUnramifiedValuation` |

Lines 126–128 are the doc comment, line 129 the `noncomputable def` keyword
and name, lines 130–137 the parameters and result type, and lines 138–139 the
body. The source module opens namespace `LocalFieldTheory` (line 22), works in
`noncomputable section` (line 26), declares `universe u` (line 28) and opens
`ValuativeRel` notation (line 30); the adapted module does the same in
`Langlands.NYLL.LocalFieldTheory`.

Worker 3 made these changes on 13 November 2026:

- added the `Langlands.NYLL` namespace prefix. The two ingredients and the
  unramified class are the published prefixed declarations of the same names.
  The source spells the class
  `LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`;
  inside `Langlands.NYLL.LocalFieldTheory` the shorter spelling resolves to
  the published class;
- kept the parameters, their order, the result type and the body exactly;
- wrote `def` inside the module's `noncomputable section` instead of
  `noncomputable def`;
- rewrote the doc comment to describe the adapted definition;
- replaced the source imports by the two published modules above.

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
