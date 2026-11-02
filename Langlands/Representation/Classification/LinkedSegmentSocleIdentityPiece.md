# Generic helpers for the identity geometric piece

Author: Worker 1033.

This module provides generic tensor, matrix-entry and transport lemmas. The
overlapping case of `LinkedSegmentSocleReverseProductQuotientHom` (Zelevinsky
1980, Proposition 4.6, step (2)) uses them. Everything lives in the namespace
`Langlands.Classification.QuotientHom`. Nothing here concerns segments. These
are internal helpers, not results from the literature. The module is the first
of five supporting modules for the exact proof task ba6ec030; the chain ends in
[LinkedSegmentOverlapAssembly](LinkedSegmentOverlapAssembly.md).

## Tensor products

- `compEquivOfEq ρ h`: if two monoid homomorphisms `f g : H →* G` agree
  pointwise, the identity linear map is an equivalence
  `Representation.Equiv (ρ.comp f) (ρ.comp g)`.
- `tprodAssocEquiv ρ σ τ`: for three representations of one monoid,
  `TensorProduct.assoc` is an equivalence between `(ρ ⊗ σ) ⊗ τ` and
  `ρ ⊗ (σ ⊗ τ)`, with `Representation.tprod` as the tensor product. The proof
  checks the intertwining identity on pure tensors with
  `TensorProduct.ext_threefold`.
- `externalTwoEquiv ρ`: let `ρ i` be representations of groups `H i` for
  `i : Fin 2`. Their external tensor product `FiniteTensor.external ρ` is
  equivalent to the tensor product of `ρ 0` and `ρ 1`, each pulled back to
  `∀ i, H i` along the coordinate evaluation `Pi.evalMonoidHom`. The linear
  equivalence is the published `FiniteTensor.headTailLinearEquiv`, followed on
  the tail by `PiTensorProduct.subsingletonEquiv` for the one-element index
  type `Fin 1`. Intertwining is checked on pure tensors.

## Matrix entries of refined Levi elements

- `refinedLevi_entry B S x i t a b`: an entry of the inner block `t` of the outer
  block `i` of `(refinedLeviEquiv R B S).symm x` is the entry of the ambient
  matrix `B.leviEmbedding R x.val`. Its coordinates are
  `B.index i ((S i).index t a)` and `B.index i ((S i).index t b)`. The proof
  rewrites `x` as the image of its inverse image. It then applies
  `BlockShape.leviEmbedding_apply_same` twice.
- `refinedLevi_outer_entry`: the same statement one level up. The outer block
  `i`, embedded by `(S i).leviEmbedding`, has the entries of the ambient
  matrix at `B.index i a` and `B.index i b`.
- `refinedLevi_entry_eq`: two refined Levi elements, for possibly different
  shapes `B`, `C` and refinements, can have equal ambient matrices. Then their
  inner entries agree at coordinates with the same ambient positions. The
  proof uses `refinedLevi_entry` twice.

## Transport

- `intersectionTransportEquivOne B C ψB ψC hψ σ ρ e`: this is the identity
  permutation case of the published intersection transport. Let `σ` be a
  representation of `sourceLevi F B C 1` with an equivalence `e` to `ρ.comp ψB`,
  where `ρ` is a representation of any monoid `P`. Suppose also that
  `ψB x = ψC y` whenever `x` and `y` have the same ambient matrix. Then
  `intersectionTransport F B C 1 σ` is equivalent to `ρ.comp ψC`. The linear map
  is that of `e`. For intertwining, the published
  `intersectionLeviConjugation_symm_embedding` shows that at `w = 1` the inverse
  conjugation preserves the ambient matrix, so `hψ` applies. This gives the
  `key` step. The statement and the `key` step are mine. The rest of the proof,
  from `refine Representation.Equiv.mk e.toLinearEquiv` on, is adapted line for
  line from the published `SegmentEdge.intersectionTransportEquivOf` of
  `Classification/SegmentEdgeJacquetReduction` (Worker 890, artifact
  `936ff465-c0b4-4e1f-8c8a-ef6139f08699`, task
  `b331611c-526d-4925-87fe-ea67ed6e6fed`). That declaration pulls the target
  back to a third Levi through `transport`. Here the target is pulled back to
  an arbitrary monoid `P`, which the identity case needs.

## Imported helpers

Two helpers come from published modules imported here; this module does not
restate them.

- `Langlands.CuspidalSupport.LeviAdmissibility.index_val` from
  `CuspidalSupport/LeviSplitContraction` (artifact
  `c862f739-656d-4705-89a9-0db3bfc7d716`, task
  `e1237fc1-de75-4a4d-924b-d509dc475361`). It computes the ambient coordinate
  `B.index i b` as `∑_{k < i} B.size k + b`.
  [LinkedSegmentOverlapShapes](LinkedSegmentOverlapShapes.md) uses it.
- `Langlands.Classification.SegmentEdge.subgroupEqualityCompEquiv` from
  `Classification/SegmentEdgeJacquetReduction` (artifact
  `936ff465-c0b4-4e1f-8c8a-ef6139f08699`, task
  `b331611c-526d-4925-87fe-ea67ed6e6fed`). It relabels a representation along
  an equality of subgroups and keeps an equivalence with a pulled-back
  representation.
  [LinkedSegmentOverlapInduction](LinkedSegmentOverlapInduction.md) uses it.

Both modules are already in the import closure of the published step (1) and
Proposition 3.4 proofs on which the main proof depends.
