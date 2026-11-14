# Uniformizer-power maps to ideal powers and successive quotients

The two maps are the original valuation-ring-linear multiplication map r ↦ r * ϖ^n into the n-th maximal-ideal power and its composite with the actual successive quotient projection. The four propositions state the normalized values −1 and +1 of the chosen prime-element field unit and its inverse, identify the quotient-map kernel with the maximal ideal and assert its surjectivity.

## Pinned source and attribution

Naganori Yamaguchi (assisted by OpenAI Codex), `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`. Registered original `external-lean-reuse-snapshots-2026-10-21`, content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The retained original file SHA-256 is `8c7082cb0e2e8ac6db22ff1afd4a1d173032246eac681ed075bb9feab7c5f71e`. The readable snapshot is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

The original copyright/Apache-2.0/author header is retained in the Lean file. The unchanged original license and notices are `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Worker 194 made the extraction and adaptations recorded below on 14 November 2026.

## Exact source correspondence

| Source unit and lines | Original declaration | Published declaration |
| --- | --- | --- |
| M133.018, 265–272 | `LocalFieldTheory.v_integerRingUniformizerFieldUnit` | `Langlands.NYLL.LocalFieldTheory.v_integerRingUniformizerFieldUnitStatement` |
| M133.019, 277–285 | `LocalFieldTheory.v_inverseIntegerRingUniformizerFieldUnit` | `Langlands.NYLL.LocalFieldTheory.v_inverseIntegerRingUniformizerFieldUnitStatement` |
| M133.025, 400–411 | `LocalFieldTheory.maximalIdealPowMulUniformizerPowMap` | `Langlands.NYLL.LocalFieldTheory.maximalIdealPowMulUniformizerPowMap` |
| M133.027, 425–431 | `LocalFieldTheory.maximalIdealPowSuccQuotMulUniformizerPowMap` | `Langlands.NYLL.LocalFieldTheory.maximalIdealPowSuccQuotMulUniformizerPowMap` |
| M133.029, 446–460 | `LocalFieldTheory.maximalIdealPowSuccQuotMulUniformizerPowMap_ker` | `Langlands.NYLL.LocalFieldTheory.maximalIdealPowSuccQuotMulUniformizerPowMap_kerStatement` |
| M133.030, 464–485 | `LocalFieldTheory.maximalIdealPowSuccQuotMulUniformizerPowMap_surjective` | `Langlands.NYLL.LocalFieldTheory.maximalIdealPowSuccQuotMulUniformizerPowMap_surjectiveStatement` |

Line ranges include each complete original declaration and any original proof; only its signature and proposition are retained for a statement target. The definition names above denote the constructions themselves. The statement names above denote propositions, without proofs of those propositions.

## Telescope, construction and modifications

Each declaration retains (K : Type u), [Field K], [ValuativeRel K], [TopologicalSpace K] and [IsNonarchimedeanLocalField K], in source order. Each map and its kernel/surjectivity target then takes explicit ϖ : 𝒪[K], hϖ : Irreducible ϖ and n : Nat, in that order. There is no restriction to the chosen uniformizer in these four declarations. The two normalized-value targets use the published integerRingUniformizerFieldUnit and inverseIntegerRingUniformizerFieldUnit and preserve the source sign convention. The source LocalFieldTheory.IsNonarchimedeanLocalField.v is explicitly prefixed by Langlands.NYLL. In the linear map, the membership proof is the published M133.023 theorem, and map_add' and map_smul' retain the original ext/simp proofs. The quotient map is exactly maximalIdealPowSuccQuotMk.comp of that linear map. No extra instance, kernel proof, surjectivity proof or evaluation theorem is introduced.

The source namespace is adapted to the namespace displayed in the name table. Original whole-module imports are replaced by these focused imports:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U007.Definitions`
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U023.Proofs`
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.MaximalIdealDefinitions`

Each theorem is changed to a `def` returning `Prop`: the full ordered telescope is retained, and the source conclusion becomes its body. Source theorem proofs and theorem attributes are omitted. Construction bodies and any proof terms inside them are unchanged apart from resolving source names to their published adaptations. Documentation comments are replaced with focused unit labels; unrelated source declarations and unused opens are omitted. No new global or local instance is declared. These support units assert no host class-formation, cup, transfer, Tate or reciprocity comparison.

## Lean declarations

The following is the exact authored declaration content, in its declared namespace and context.

```lean
noncomputable section

universe u

open scoped ValuativeRel

/-- Source M133.018: exact proposition target. -/
def v_integerRingUniformizerFieldUnitStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
    Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v K
      (Additive.ofMul (integerRingUniformizerFieldUnit K)) = -1

/-- Source M133.019: exact proposition target. -/
def v_inverseIntegerRingUniformizerFieldUnitStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
    Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v K
      (Additive.ofMul (inverseIntegerRingUniformizerFieldUnit K)) = 1

/-- Source M133.025: original construction. -/
def maximalIdealPowMulUniformizerPowMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝒪[K] →ₗ[𝒪[K]] ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) where
  toFun r := ⟨r * ϖ ^ n, mul_uniformizer_pow_mem_maximalIdeal_pow K ϖ hϖ n r⟩
  map_add' r s := by
    ext
    simp [add_mul]
  map_smul' a r := by
    ext
    simp [mul_assoc]

/-- Source M133.027: original construction. -/
def maximalIdealPowSuccQuotMulUniformizerPowMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝒪[K] →ₗ[𝒪[K]] MaximalIdealPowSuccQuot K n :=
  (maximalIdealPowSuccQuotMk K n).comp
    (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n)

/-- Source M133.029: exact proposition target. -/
def maximalIdealPowSuccQuotMulUniformizerPowMap_kerStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) : Prop :=
    LinearMap.ker (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n) =
      (𝓂[K] : Ideal 𝒪[K])

/-- Source M133.030: exact proposition target. -/
def maximalIdealPowSuccQuotMulUniformizerPowMap_surjectiveStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) : Prop :=
    Function.Surjective (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n)
```
