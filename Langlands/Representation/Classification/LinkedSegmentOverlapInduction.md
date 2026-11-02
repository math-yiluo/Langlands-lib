# The induced side of the identity piece

Author: Worker 1033.

Fix an overlap configuration `O : OverlapConfig T n` (see
[LinkedSegmentOverlapShapes](LinkedSegmentOverlapShapes.md)). The published
identity geometric piece `geometricPieceFunctor T O.B O.C 1 O.S O.R _ _` is the
composite of five published functors:

1. the normalized refined Jacquet functor for `(B, S)`;
2. relabeling along a subgroup equality;
3. the intersection transport at the identity permutation;
4. relabeling again;
5. the normalized refined induction for `(C, R)`.

This module rewrites steps 2–5 in terms of the common product
`P = GL(deg Δ) × GL(deg init) × GL(deg term)`. It lives in the namespace
`Langlands.Classification.QuotientHom`. All results are internal
constructions on top of published equivalences.

## Generic helpers

- `equivOfApplyEq ρ σ h`: two representations on one space with the same
  action are equivalent through the identity.
- `tripleTensor ρ₀ ρ₁ ρ₂`: the external tensor product of three actions,
  as a representation of `G₀ × G₁ × G₂` on `V₀ ⊗ (V₁ ⊗ V₂)`. It is the
  `Representation.tprod` of the three actions pulled back along the
  projections.
- `reindex_finCongr_symm_self`: reindexing `GL_a` along `finCongr` of a proof of
  `a = a` is the identity. Checked entrywise by `rfl`.
- `oneBlockInducedEquiv m hm π`: normalized parabolic induction from the
  one-block shape `oneBlock m hm` of the external tensor of the single factor
  `π` is equivalent to `π`. It composes the published
  `T.singleBlockNormalizedProductEquiv` with `reindex_finCongr_symm_self`.
- `inducedEquivOfEq B' hm hB σ π hσ`: the same for a shape `B'` equal to the
  one-block shape and a factor `σ` heterogeneously equal to the external tensor
  of `π`. The proof substitutes both equalities and applies
  `oneBlockInducedEquiv`. Callers pass `rfl` and `HEq.rfl`. Stating it with
  equality hypotheses avoids a slow definitional unfolding at the call site.

## Steps 2–4: transport

`transportedPieceEquiv O X τ eJ`: suppose the normalized refined Jacquet module
`(T.normalizedRefinedJacquetFunctor O.B O.S).obj X` is equivalent to
`τ.comp O.φB`, for some representation `τ` of `P`. Then its relabeled
intersection transport is equivalent to `τ.comp O.φC`. Here the relabeling uses
the subgroup equalities `O.hS.2.1.symm` and `O.hR.2.1`. The proof chains:

- the published `SegmentEdge.subgroupEqualityCompEquiv` (see
  [LinkedSegmentSocleIdentityPiece](LinkedSegmentSocleIdentityPiece.md)) for
  the first relabeling;
- `intersectionTransportEquivOne`, whose compatibility hypothesis is
  `O.coords_compat`;
- `SegmentEdge.subgroupEqualityCompEquiv` for the second relabeling;
- `compEquivOfEq`, which removes the composite
  `subgroupCongr ∘ subgroupCongr.symm` by `MulEquiv.apply_symm_apply`.

## Step 5: the target factors

- `unionBlocks O A₀ π₁` is the pair of blocks `(A₀, π₁)` of `unionShape`, with
  `A₀` a smooth representation of `GL(deg Δ)` and `π₁` one of `GL(deg init)`.
- `targetFactors O A₀ π₁ π₂` is the family of inducing factors for `(C, R)`:
  - on the refined union block, the external tensor of `unionBlocks A₀ π₁`;
  - on the intersection block, the external tensor of the single factor `π₂`.
- `inducingEquiv O A₀ π₁ π₂` identifies the published inducing representation
  `Parabolic.RefinedInductionTensor.inducingRepresentation F T O.C O.R
  (targetFactors A₀ π₁ π₂)` with `(tripleTensor A₀ π₁ π₂).comp O.φC`. The
  proof splits the two-factor external tensor with `externalTwoEquiv`. It
  splits the union block the same way and identifies the one-block factor
  with `π₂` by the published `singleBlockTensorEquiv`. It then pulls back along
  the inverse `refinedLeviEquiv`, using the published
  `FiniteTensorFiltration.compCongr` and `tprodCongr`. Finally it reassociates
  with `tprodAssocEquiv`. The remaining identifications are equalities of
  actions (`equivOfApplyEq` with `rfl`).
- `inducedTermEquiv O A₀ π₁ π₂`: the induced intersection block
  `blockRepresentations F T O.C O.R (targetFactors A₀ π₁ π₂) 1` is equivalent to
  `π₂`. This is `inducedEquivOfEq` with `rfl` and `HEq.rfl`.
- `nonempty_inducedPieceEquiv O A₀ π₁ π₂`: the published external
  representation of the target factors is equivalent to the tensor product of
  the induced union block, pulled back along evaluation at `0`, and `π₂`,
  pulled back along evaluation at `1`. The proof composes `externalTwoEquiv`
  with `inducedTermEquiv` on the second factor. The result is stated as
  `Nonempty` of an equivalence, because the composite as a `def` times out
  during elaboration.
