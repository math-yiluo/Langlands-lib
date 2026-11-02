# A nonzero map out of the product of two overlapping segment socles

Author: Worker 1033.

This module contains the Frobenius-reciprocity core of step (2) of Zelevinsky
1980, Proposition 4.6 (printed p. 186), in the overlapping case. Zelevinsky
reduces `Hom(π, ω) ≠ 0` to `Hom(σ, ⟨Δ∪⟩ ⊗ ⟨Δ∩⟩) ≠ 0` by Frobenius reciprocity
(Ze80 1.1), where `σ` is the Jacquet module of `π` along `(deg Δ∪, deg Δ∩)`.
He then exhibits a quotient of `σ` that maps onto `⟨Δ∪⟩ ⊗ ⟨Δ∩⟩`. The theorem
below is that argument for the shapes of an `OverlapConfig` (see
[LinkedSegmentOverlapShapes](LinkedSegmentOverlapShapes.md)). The required
quotients are hypotheses here. In particular, the natural surjection `η` onto
the identity geometric piece (Ze80, Corollary 1.3, printed p. 171) is assumed,
not proved. Everything lives in the namespace
`Langlands.Classification.QuotientHom`.

This is a supporting module for the exact proof of
`LinkedSegmentSocleReverseProductQuotientHom` (Ze80 4.6, step (2)). By itself
it does not prove that statement. Its provenance is internal: it formalizes
Zelevinsky's Frobenius-reciprocity step for the concrete Library functors, and
it asserts no new literature result.

## Generic intertwiner lemmas

- The pullback of an intertwiner along a monoid homomorphism is the published
  `Langlands.Classification.SegmentSocleJacquetReduction.compMap φ f`
  (Worker 756, part of the Ze80 3.4 proof, module
  `Classification/SegmentSocleJacquetReduction`, artifact
  `dbcb1209-e019-4728-b23b-3e10b06ad990`, task
  `b95105c6-f8bb-4641-ae53-2f49d1e7f034`). This module imports it.
- `tprodMap f g`: the tensor product of two intertwiners of one monoid is an
  intertwiner of the tensor product representations
  (`TensorProduct.map`, checked on pure tensors). Its linear map is the one
  used in the published `Langlands.MixedProductTensor.externalMap` (Worker 837,
  `Mirabolic/MixedProducts`, artifact `7aa675e1-c7d5-4f42-b6b4-3b5fcd2cdc6c`,
  task `f5488c8d-59a8-4de8-8649-4511bbaea5d9`). That map is for external tensor
  products, and the intertwining proof here is my own.
- `tprodMap_surjective`, `compMap_surjective`, `comp_surjective`,
  `equiv_surjective`: surjectivity of `tprodMap` (from
  `TensorProduct.map_surjective`), of the published `compMap`, of composites,
  and of equivalences. They are stated separately so that the composite
  surjectivity proof below does not unfold the composite maps.
- `nontrivial_of_isIrreducible`: an irreducible representation lives on a
  nontrivial space. This uses the published
  `Representation.irreducible_iff_isSimpleModule_asModule` and
  `IsSimpleModule.nontrivial`.
- `ne_zero_of_surjective_of_nontrivial`: a surjective intertwiner onto a
  nontrivial space is nonzero.

## The core theorem

`OverlapConfig.exists_ne_zero_of_identityPiece O A π₁ π₂ E₁ E η hη f₀ hf₀ f₁ hf₁
hE₀ hE₁` takes the following data:

- source blocks `A i` for the shape `B` and target blocks `E j` for the shape
  `C`, with `E 0` and `E 1` irreducible;
- the hypothesis `E₁` of
  [LinkedSegmentOverlapPiece](LinkedSegmentOverlapPiece.md), saying that the
  Jacquet module of `A 1` along the split of `Δ'` is `π₁ ⊗ π₂`;
- a natural transformation `η` from the published `jacquetInductionFunctor T O.B
  O.C` to the published identity geometric piece
  `geometricPieceFunctor T O.B O.C 1 O.S O.R _ _`, whose component `hη` at
  `externalSmoothObject A` is surjective;
- a surjective intertwiner `f₀` from the induced union block of
  `targetFactors (A 0) π₁ π₂`, which is the normalized induction of `A 0 ⊗ π₁`
  to `GL(deg U)`, onto `E 0`;
- a surjective intertwiner `f₁ : π₂ → E 1`.

It concludes that there is a nonzero intertwiner from the normalized product
induction of `A` along `B` to the normalized product induction of `E` along
`C`.

Proof. Let `eG` be the equivalence of `nonempty_geometricPieceEquiv`, from the
identity geometric piece to (induced union block) ⊗ `π₂`. Let `g` be
`tprodMap` of `f₀` and `f₁`, each pulled back along a coordinate evaluation.
Let `eE` be `externalTwoEquiv` for `E`. The composite

    c = eE⁻¹ ∘ g ∘ eG ∘ η_A

maps the normalized Jacquet module along `C` of the induced representation onto
`C.blockTensor E`. It is surjective by the generic lemmas, and nonzero
because `E 0 ⊗ E 1` is nontrivial. The published first adjointness
`Parabolic.FirstAdjointness.equiv T O.C _` is a linear equivalence
`Hom(π, i_C σ) ≃ Hom(r_C π, σ)`. Its inverse sends `c` to a nonzero
intertwiner into `i_C(C.blockTensor E)`. That is the normalized product
induction of `E` along `C`.

The theorem has a raised heartbeat limit.
