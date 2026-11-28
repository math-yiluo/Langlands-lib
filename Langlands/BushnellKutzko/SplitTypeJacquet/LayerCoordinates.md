# The unit groups of a lattice chain in adapted coordinates

Module `Langlands.BushnellKutzko.SplitTypeJacquet.LayerCoordinates`. Notation of `LayerBasis`;
`ν : ι ≃ Σ i, Fin (d i)` numbers the adapted basis by a finite index type `ι`, and
`coordBasis L b hϖ ν` is the reindexed basis.

- `toLin_coordBasis_mem_endFiltration_iff` restates the criterion of `LayerBasis` in the
  reindexed coordinates. If a block function `blk` on `ι` reverses the order of the layers
  (`(ν c).1 < (ν c').1 ↔ blk c' < blk c`), then the order `𝔄(L)` and the radical `End^1(L)`
  become `InOrd blk` and `InRad blk` (`toLin_coordBasis_mem_order_iff`,
  `toLin_coordBasis_mem_endFiltration_one_iff`).
- `stdToAut L b hϖ ν : GL ι F ≃* Aut_F(V)` lets a matrix act through the reindexed basis. For
  a block function `blk` reversing the order of the layers as above,
  `stdToAut_mem_unitFiltration_zero_iff` and `stdToAut_mem_unitFiltration_one_iff` identify the
  unit groups `U(𝔄)` and `U^1(𝔄)` with `J0 F blk` and `J1 F blk`.
- `layerReduction_stdToAut_apply`: for such `blk` and `x ∈ J0 F blk`, the matrix of the reduction of
  `stdToAut x` on the layer `L_i / L_(i+1)` in the basis `b i` (the Library's
  `LatticeChain.layerReduction`) has entries the residues of the entries of `x` in the diagonal
  block of the layer `i`. Proof: apply `layerReduction_spec` to the lift of `b i s`. In the image,
  the terms of the later layers lie in `L_(i+1)`, the terms of the earlier layers have
  coefficients in the maximal ideal, and the remaining terms reduce termwise
  (`intervalMk_sum_smul`).
