# The Galois-to-residue isomorphism of an unramified extension

This module adapts NYLL source unit M161.036. It exports one data definition,
`Langlands.NYLL.LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure`.
It is the group isomorphism `Gal(L/K) ≃* Aut(𝓀[L]/𝓀[K])` of a finite Galois
unramified extension of nonarchimedean local fields, which sends `σ` to the
automorphism it induces on the residue field. The field arithmetic Frobenius
M264.007 is defined from it: it is the inverse image of the residue
arithmetic Frobenius.

## Interface and meaning

```lean
def galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L / K) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])
```

The level parameter `u` is the only universe; `K` and `L` share it, as in the
source. The parameters, in order, are exactly those of the source definition:

| Parameter | Meaning |
| --- | --- |
| `K L : Type u` | the base and extension fields |
| `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` | `K` is a nonarchimedean local field (Mathlib's class) |
| the same four for `L` | `L` is a nonarchimedean local field |
| `[Algebra K L] [FiniteDimensional K L] [IsGalois K L]` | `L/K` is a finite Galois extension |
| `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]` | the valuation of `L` extends that of `K`; this gives the algebras `𝒪[K] → 𝒪[L]` and `𝓀[K] → 𝓀[L]` |
| `[IsIntegralClosure 𝒪[L] 𝒪[K] L]` | `𝒪[L]` is the integral closure of `𝒪[K]` in `L` |
| `[Module.Finite 𝒪[K] 𝒪[L]]` | `𝒪[L]` is a finite `𝒪[K]`-module |
| `[IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]` | the published class (M161.001): the maximal ideal `𝓂[L]` has ramification index one over `𝒪[K]` |

`𝒪[F]`, `𝓂[F]` and `𝓀[F]` are Mathlib's scoped `ValuativeRel` notation for
the integer ring `Valuation.integer (ValuativeRel.valuation F)`, its maximal
ideal and its residue field. `Gal(L / K)` is `L ≃ₐ[K] L` with Mathlib's group
structure. The codomain is the group of `𝓀[K]`-algebra automorphisms of
`𝓀[L]`, for the residue algebra induced by the integer-ring algebra of the
valuation extension. The two integer-ring hypotheses are Prop-valued, so the
value does not depend on which proofs of them are supplied. No instance is
declared.

## Construction

The complete body is the source body:

```lean
  MulEquiv.ofBijective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation K L)
```

- `galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L` is the published
  group homomorphism `Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])` (M160.006, in
  [the residue algebra definitions](../ResidueGalois/AlgebraDefinitions.md)).
  It sends `σ` to the residue automorphism induced by the restriction of `σ`
  to `𝒪[L]`.
- `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation K L`
  is the published proof (M161.035, in
  [the bijectivity proof](ResidueBijectiveProof.md)) that this homomorphism is
  bijective. Its type is the published target
  `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuationStatement`
  (in [the bijectivity target](ResidueBijectiveStatement.md)) at universe `u`,
  applied to the same parameters.
- Mathlib's `MulEquiv.ofBijective` turns a bijective multiplicative
  homomorphism into a multiplicative equivalence with the same forward map.

So the forward map of the definition is, by definition, the residue
homomorphism: `galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L σ`
is `galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L σ`, which is the
published `galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ`. The source
records this as the theorem M161.037 (proved by `rfl`); it is not exported here.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings.

## Imports and scope

The only import is the published proof module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueBijectiveProof`.
It supplies the bijectivity theorem and, through its imports, the residue
homomorphism, the class `IsUnramifiedValuedExtension`, Mathlib's
`IsNonarchimedeanLocalField`, `IsGalois`, `IsIntegralClosure`, `MulEquiv` and
the residue-field notation. The source module's other imports serve its
remaining declarations.

Only M161.036 is adapted. The source theorems M161.037 (the `_apply` lemma),
M161.038 and the rest of the source module are not ported here.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean#L794-L806)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, readable in the project
snapshot under `n-yamaguchi-0729--ClassFieldTheory/source/`. The full file has
SHA-256 `b9c37585002a07b55997dd84ffdc7409fa5fee34fea04889196a4f617ddb909d`.

| Partition unit | Original definition in `LocalFieldTheory` | Original lines | Adapted definition in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- | --- |
| M161.036 | `galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure` | 794–806 | `galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure` |

Lines 794–795 are the doc comment, line 796 the `noncomputable def` keyword
and name, lines 797–804 the parameters and result type, and lines 805–806 the
body. The source module declares `universe u` (line 26) and works in
`noncomputable section` (line 24) in namespace `LocalFieldTheory` (line 22);
the adapted module does the same in `Langlands.NYLL.LocalFieldTheory`. The
unit identifier comes from the
[public declaration partition](../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m161).

Worker 3 made these changes on 13 November 2026:

- added the `Langlands.NYLL` namespace prefix. The residue homomorphism, the
  bijectivity theorem and the unramified class are the published prefixed
  declarations of the same names. The source spells the class
  `LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`;
  inside `Langlands.NYLL.LocalFieldTheory` the shorter spelling resolves to
  the published class;
- kept the parameters, their order, the result type and the body exactly;
- wrote `def` inside the module's `noncomputable section` instead of
  `noncomputable def`;
- rewrote the doc comment to describe the adapted definition;
- replaced the source imports by the published proof module above.

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
