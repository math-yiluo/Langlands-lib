# The degree-two comparison for abelian varieties from a creation-contraction family

Module `Langlands.AbelianScheme.DegreeTwoComparisonFinal`, namespace `Langlands.AbelianScheme`.

## Purpose

`DegreeTwoComparisonAssembly.exists_comparison_of_inputs` reduces
`FieldH2ExteriorCoproductComparisonStatement` for an abelian scheme `A` over a field `K` to three
inputs:

1. injectivity of `degreeTwoMap A`,
2. alternation of the cup product `cupA A`,
3. a bounded creation-contraction family on `Hⁿ(A) = structureCohomology A.X n`.

This module supplies the first input unconditionally. It derives the second input from the third,
so the creation-contraction family is the only remaining hypothesis.

Notation: `P = A.X ⨯ A.X`, `p₁ = prod.fst`, `p₂ = prod.snd`, `f^* = pullStructure A f n`.

## Injectivity

- `mixedTensorA_eq_mixedTensor`: `mixedTensorA A` equals
  `AllSeq.mixedTensor p₁ p₂ (cover A) (cover A) …` on the cover
  `CanonicalDegreeTwoSum.productCover A = prodCover p₁ p₂ (cover A) (cover A)`. That cover is the
  same family as `mixedCover A`. The two maps are compared on pure tensors (`TensorProduct.ext'`),
  using `mixedTensorA_tmul_eq_mixedCover`, `AllSeq.mixedTensor_tmul` and `AllSeq.mixedCup_apply`.
- `degreeTwoMap_eq_sumMap`: `degreeTwoMap A = CanonicalDegreeTwoSum.sumMap A`. Both maps send
  `(a, t, b)` to `p₁^* a + (mixed tensor of t) + p₂^* b`; they differ only in how the sum is
  bracketed.
- `degreeTwoMap_injective`: `degreeTwoMap A` is injective. This follows from
  `CanonicalDegreeTwoSum.sumMap_injective A`, which has no hypotheses.

## Alternation and the comparison for `A`

Fix the following data:

- a finite index type `I : Type v` with decidable equality;
- linear maps `c i n : Hⁿ(A) ⟶ Hⁿ⁺¹(A)` and `d i n : Hⁿ⁺¹(A) ⟶ Hⁿ(A)`.

Assume:

- `hrel`: `d i (n+1) ∘ c j (n+1) + c j n ∘ d i n = if i = j then id else 0`;
- `hbound`: `Hⁿ(A)` is a `Subsingleton` for `n > card I`;
- `w : I → H¹(A)` with `hspan : span K (range w) = ⊤`;
- `hcup : c i 1 x = cupA A (w i) x`;
- `hzero : c j 0 (d i 0 (w j)) = if i = j then w j else 0`.

Results:

- `cupA_self_eq_zero_of_CAR`: `cupA A x x = 0` for every `x`. This is
  `BoundedCreationContraction.cup_self_eq_zero` applied with `B = cupA A` and the skew-symmetry
  `cupA_swap A`. It holds in every characteristic.
- `exists_comparison_of_CAR`: the conclusion of the target for `A`. There exist
  `e : H²(A) ≃ₗ[K] ⋀[K]^2 H¹(A)` and `κ : H²(P) ≃ₗ[K] H²(A) × ⨂[K]^2 H¹(A) × H²(A)` such that
  `κ (p₁^* x) = (x, 0, 0)`, `κ (p₂^* x) = (0, 0, x)` and
  `κ ((p₁ * p₂)^* x) = (x, toTensorPower (e x), x)`. The proof applies
  `exists_comparison_of_inputs` to `degreeTwoMap_injective` and `cupA_self_eq_zero_of_CAR`.

## The creation-contraction package and the target

- `CARFamily A` (universe parameters `u` of `K` and `v` of the index type) bundles the data and
  hypotheses listed above. Its fields are `I`, `fintype`, `decEq` (registered as instances),
  `c`, `d`, `rel` (`hrel`), `bound` (`hbound`), `w`, `span_eq_top` (`hspan`), `c_one` (`hcup`) and
  `c_zero_d_zero` (`hzero`).
- `exists_comparison_of_CARFamily A F` is `exists_comparison_of_CAR` applied to the fields of `F`.
- `fieldH2ExteriorCoproductComparison_of_CARFamily`: if `Nonempty (CARFamily.{u, v} A)` holds for
  every field `K : Type u` and every abelian scheme `A` over `Spec K`, then
  `FieldH2ExteriorCoproductComparisonStatement.{u}` holds. The universe `v` of the index type is
  free, so `I = Fin g` is allowed.

## The degree bound from the `H¹` dimension

- `finrank_structureCohomology_one_le_card A w hspan`: if `w : I → H¹(A)` spans, then
  `finrank K H¹(A) ≤ card I`. This is Mathlib's `finrank_range_le_card` with `span (range w) = ⊤`.
- `CARData A` (universes `u`, `v`) has the same fields as `CARFamily A` except `bound`. Its
  fields `fintype` and `decEq` are registered as instances.
- `CARData.toCARFamily A hH1 D` is a definition. From
  `hH1 : FieldStructureSheafH1DimensionStatement.{u}` and `D : CARData A` it builds a `CARFamily A`
  with the same fields. The bound `Hⁿ(A) = 0` for `n > card I` is
  `subsingleton_structureCohomology_of_finrank_lt_of_H1Dimension` (from
  `StructureCohomologyVanishing`), applied to `finrank K H¹(A) ≤ card I < n`.
- `fieldH2ExteriorCoproductComparison_of_H1Dimension_of_CARData`: assume
  `FieldStructureSheafH1DimensionStatement.{u}`, and assume `Nonempty (CARData.{u, v} A)` for
  every field `K : Type u` and every abelian scheme `A` over `Spec K`. Then
  `FieldH2ExteriorCoproductComparisonStatement.{u}` holds.

## Scope

The creation-contraction family (or datum) is a hypothesis; this module does not construct it.
`FieldStructureSheafH1DimensionStatement` is also a hypothesis of the last theorem; it is not
proved here. No excluded Picard, dual-scheme or representability statement and no proof of
`FieldH2PrimitiveInjectivityStatement` is imported.

## Provenance

This is an internal derivation and contains only assembly steps. The mathematical inputs are the
published and accepted Library results cited above: `CanonicalDegreeTwoSum.sumMap_injective`,
`BoundedCreationContraction.cup_self_eq_zero`,
`DegreeTwoComparisonAssembly.exists_comparison_of_inputs` and
`subsingleton_structureCohomology_of_finrank_lt_of_H1Dimension` (module
`Langlands.AbelianScheme.StructureCohomologyVanishing`).
