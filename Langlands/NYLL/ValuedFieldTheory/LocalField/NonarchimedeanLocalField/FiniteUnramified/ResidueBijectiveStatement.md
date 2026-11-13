# Bijectivity of the residue action of an unramified extension: target

This module states NYLL source unit M161.035 as a closed proposition. It
exports one Prop-valued definition,
`Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuationStatement`.
Nothing is proved here; the proof is a separate unit under the adapted source
name
`Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation`.

Mathematically, the target says: let `L/K` be a finite Galois extension of
nonarchimedean local fields whose valuation extends that of `K`, and suppose
the maximal ideal of the integer ring `𝒪[L]` has ramification index one over
`𝒪[K]`. Then every `𝓀[K]`-algebra automorphism of the residue field `𝓀[L]` is
induced by exactly one element of `Gal(L/K)`. In other words, the residue map
`Gal(L/K) → Aut(𝓀[L]/𝓀[K])` is a group isomorphism. This is the classical
statement that an unramified extension of local fields has Galois group
isomorphic to that of its residue extension. It feeds the definition of
the field arithmetic Frobenius M264.007, through the isomorphism M161.036.

## The proposition

```lean
def galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuationStatement :
    Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L],
    Function.Bijective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)
```

The level parameter `u` is the only universe; `K` and `L` share it, as in the
source. The quantified binders, in order, are exactly the parameters of the
source theorem:

| Binder | Meaning |
| --- | --- |
| `K L : Type u` | the base and extension fields |
| `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` | `K` is a nonarchimedean local field (Mathlib's class: valuative topology, locally compact, nontrivial valuation) |
| the same four for `L` | `L` is a nonarchimedean local field |
| `[Algebra K L] [FiniteDimensional K L] [IsGalois K L]` | `L/K` is a finite Galois extension |
| `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]` | the valuation of `L` extends that of `K`; this gives the algebra `𝒪[K] → 𝒪[L]` and the residue algebra `𝓀[K] → 𝓀[L]` |
| `[IsIntegralClosure 𝒪[L] 𝒪[K] L]` | `𝒪[L]` is the integral closure of `𝒪[K]` in `L` |
| `[Module.Finite 𝒪[K] 𝒪[L]]` | `𝒪[L]` is a finite `𝒪[K]`-module |
| `[IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]` | the maximal ideal `𝓂[L]` has ramification index one over `𝒪[K]` |

The two integer-ring hypotheses are Prop-valued. They hold in the present
situation: the published theorem
`Langlands.NYLL.LocalFieldTheory.localCompleteDVF_integerRing_properties`
proves both for every finite separable extension of nonarchimedean local fields
with a valuation extension, with the integer rings written as the valuation
subrings `(ValuativeRel.valuation F).valuationSubring`; `IsGalois K L` implies
separability. The source takes them as instance arguments at this
declaration, so the target keeps them.

The conclusion is `Function.Bijective` of the underlying function of the
group homomorphism `galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L`.

### Published declarations used

- `Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure`
  (M160.006, [residue algebra definitions](../ResidueGalois/AlgebraDefinitions.md)):
  the group homomorphism `Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])` sending `σ` to
  the residue automorphism induced by the restriction of `σ` to `𝒪[L]`. It
  needs only the field, valuative, algebra, valuation-extension and
  integral-closure parameters; the remaining binders above are not used by it.
- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`
  (M161.001, [the class](Definitions.md)), here at universes `u u`. Its single
  field is
  `(𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1`. It takes the
  `Module.Finite 𝒪[K] 𝒪[L]` binder above as its instance argument.

The notation `𝒪[F]`, `𝓂[F]` and `𝓀[F]` is Mathlib's scoped `ValuativeRel`
notation for the integer ring `Valuation.integer (ValuativeRel.valuation F)`,
its maximal ideal and its residue field. `Gal(L/K)` is `L ≃ₐ[K] L` with
Mathlib's group structure (composition).

## Check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings. Inspection of the declaration reported kind
`definition`, level parameters `[u]`, `statement_returns_prop: true`, and only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Imports and scope

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.Definitions`
  supplies the class `IsUnramifiedValuedExtension` and, through its imports,
  Mathlib's `IsNonarchimedeanLocalField`.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.AlgebraDefinitions`
  supplies `galoisGroupResidueAlgEquivHomOfIsIntegralClosure` and, through its
  imports, `IsGalois`, `IsIntegralClosure` and the residue-field notation.

The source module's other imports and its remaining declarations are not
used. Only M161.035 is stated. The source's injectivity and surjectivity
theorems M161.033 and M161.034 and their inputs (the inertia-cardinality
chain and the `e · f = n` formula) are not ported here; the separate proof
unit need not follow the source's proof route. The isomorphism M161.036 is a
separate later unit.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean#L780-L792)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `b9c37585002a07b55997dd84ffdc7409fa5fee34fea04889196a4f617ddb909d`.

| Partition unit | Original theorem in `LocalFieldTheory` | Original lines | Adapted target in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- | --- |
| M161.035 | `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation` | 780–792 | `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuationStatement` |

Lines 780–781 are the doc comment, line 782 the theorem name, lines 783–790
the parameters and the conclusion, and lines 791–792 the source proof (the
pair of M161.033 and M161.034). The source module declares `universe u`
(line 26), and the theorem lies in namespace `LocalFieldTheory` (opened on line
22, outside the inner `IsNonarchimedeanLocalField` namespace that closes on
line 76). The unit identifier comes from the
[public declaration partition](../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m161).

Worker 3 made these changes on 13 November 2026:

- added the `Langlands.NYLL` namespace prefix. The residue homomorphism and the
  unramified class are the published prefixed declarations of the same
  names. The source spells the class
  `LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`;
  inside `Langlands.NYLL.LocalFieldTheory` the shorter spelling resolves to
  the published class;
- packaged the theorem type as the closed proposition above. The source's
  explicit and instance parameters become `∀`-binders, in the same order and
  of the same kinds (explicit for `K L`, instance-implicit for the rest);
- omitted the source proof;
- replaced the source imports by the two published modules above.

No draft from another worker was used.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The Lean file keeps the original copyright and author header verbatim
(copyright 2026 Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by
OpenAI Codex) and records the modifications. The Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
