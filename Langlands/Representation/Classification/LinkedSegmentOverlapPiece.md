# The identity geometric piece of two overlapping segment socles

Author: Worker 1033.

Fix `O : OverlapConfig T n` (see
[LinkedSegmentOverlapShapes](LinkedSegmentOverlapShapes.md)) and two blocks
`A i`, smooth representations of `GL(deg Δ)` and `GL(deg Δ')`. Suppose the
normalized Jacquet module of `A 1` along the split `(deg init, deg term)` of
`Δ'` is equivalent to `π₁ ⊗ π₂` (hypothesis `E₁`). This module computes the
identity geometric piece of `A 0 ⊗ A 1` for the shapes `B`, `C`. The result is
the normalized induction of `A 0 ⊗ π₁` to `GL(deg U)`, tensored with `π₂`.
This is the concrete form of the term `(⟨Δ⟩ × ⟨Δ' \ Δ∩⟩) ⊗ ⟨Δ∩⟩` in step (2) of
Zelevinsky 1980, Proposition 4.6 (printed p. 186). There, Corollary 1.3 and 3.4
produce it. The Lean computation is an internal derivation from the published
definitions of the functors. Everything lives in the namespace
`Langlands.Classification.QuotientHom`.

## Declarations

- `oneBlock_leviEmbedding m hm g`: the Levi embedding of the one-block shape
  sends `g` to its single coordinate. Proof: entrywise, with `index_zero_val`
  and the published `leviEmbedding_apply_same`.
- `jacquetPieceEquiv O A π₁ π₂ E₁` (Jacquet side, plain representations): the
  normalized refined Jacquet module of `FiniteTensor.external (A i).ρ` for
  `(B, S)` is equivalent to `(tripleTensor (A 0).ρ π₁ π₂).comp O.φB`. The proof
  chains:
  - the published `RefinedJacquetTensor.jacquetEquiv`: the refined Jacquet
    module of an external tensor is the external tensor of the factor Jacquet
    modules, pulled back along the inverse `refinedLeviEquiv`;
  - `externalTwoEquiv` for the two factors;
  - on factor `0`, the inverse of the published
    `singleBlockNormalizedJacquetEquiv`, since the Jacquet module along a
    one-block shape is the representation itself;
  - on factor `1`, the hypothesis `E₁`;
  - `oneBlock_leviEmbedding`, which identifies the remaining action.
- `nonempty_transportedJacquetEquiv`: the same for smooth representations,
  followed by the relabeling and intersection transport of the geometric
  piece. The result is equivalent to `(tripleTensor (A 0) π₁ π₂).comp O.φC`.
  The proof is `jacquetPieceEquiv` followed by `transportedPieceEquiv` of
  [LinkedSegmentOverlapInduction](LinkedSegmentOverlapInduction.md).
- `nonempty_geometricPiece_refinedEquiv`: the published identity geometric piece
  `(geometricPieceFunctor T O.B O.C 1 O.S O.R _ _).obj (externalSmoothObject A)`
  is equivalent to the published
  `Parabolic.RefinedInductionTensor.refinedRepresentation` of
  `targetFactors (A 0) π₁ π₂`. The last functor of the geometric piece is the
  normalized refined induction. The proof applies the published
  `ProductLeviCuspidalJacquetAssembly.normalizedRefinedInducedCongr` to the
  equivalence of the inducing representations. That equivalence comes from
  `nonempty_transportedJacquetEquiv` composed with the inverse of
  `inducingEquiv`.
- `nonempty_geometricPieceEquiv`: the identity geometric piece of
  `externalSmoothObject A` is equivalent to the tensor product of two
  representations of `GL(deg U) × GL(deg term)`:
  - the induced union block of `targetFactors (A 0) π₁ π₂`, pulled back along
    evaluation at `0`;
  - `π₂`, pulled back along evaluation at `1`.

  The proof composes `nonempty_geometricPiece_refinedEquiv`, the published
  refined-induction tensor theorem `Parabolic.refinedInductionTensor` (refined
  induction is the external tensor of the induced blocks), and
  `nonempty_inducedPieceEquiv`.

The three last results are stated as `Nonempty` of an equivalence, each with a
raised heartbeat limit. As definitions, the large composites time out during
elaboration.
