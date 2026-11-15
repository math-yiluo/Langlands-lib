# Weyl transport of block tensors along minimal representatives

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.PieceTransport`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`, used in the
analysis of geometric pieces. It computes the Library's Weyl transport
`CuspidalSupport.transport B C w hw` (inverse whole-Levi conjugation, as in
Bernstein–Zelevinsky 1977, §1.7) on external tensor products when `w` is a minimal
representative. The arguments are elementary computations with permutation matrices; no
hypothesis beyond those in the Lean statements is used.

## Minimal

* `isMinimalRepresentative_flatten`: if `w` is a minimal representative for `B` and `C`
  (`Geometric.IsMinimalRepresentative`: `w` is increasing on each block of `B` and `w⁻¹` on
  each block of `C`), then it is a minimal representative for the flattened shapes
  `B.flatten S` and `C.flatten R`, for any refinements `S`, `R`. Proof: by
  `BlockShape.flatten_index`, each flattened block is enumerated by an inner block
  enumeration followed by an outer one, both increasing (`Geometric.index_strictMono`).

## Entries

* `size_blockEquiv_symm`: the block bijection `CuspidalSupport.blockEquiv hw` of a
  conjugating permutation matches block sizes, `B.size (π⁻¹ j) = C.size j`.
* `leviConjugation_symm_entry_of_eq`: the Library entry formula
  `CuspidalSupport.leviConjugation_symm_block_entry`, restated for an arbitrary target block
  index `j` equal to `blockMap B C w i` (proved by substituting the equality).
* `leviConjugation_symm_apply_blockEquiv_symm`: for `m` in the target Levi, the block of
  `(leviConjugation B C w hw).symm m` at `π⁻¹ j` is the reindexing of `m j` along
  `finCongr (size_blockEquiv_symm hw j)`.

## Tensor

* `transportBlockTensorEquiv`: the transport of a block tensor `B.blockTensor ρ` is
  equivalent to the external tensor product over the target blocks `j` of
  `ρ (π⁻¹ j)` pulled back along the rank reindexing. The linear equivalence is
  `PiTensorProduct.reindex` along `π`; intertwining is checked on pure tensors using the
  previous block formula.

## Smooth

* `transportExternalCastEquiv`: for smooth factors `X k`, the transport of
  `FiniteTensor.external (X k)` is equivalent to the external tensor product of the rank
  casts `T.castRank (size_blockEquiv_symm hw j) (X (π⁻¹ j))`. Proof: compose
  `transportBlockTensorEquiv` with the factorwise equivalences `T.castRankEquiv`
  (assembled by `FiniteTensorFiltration.externalCongr`).
