# Standard coordinates for a lattice chain with cuspidal layer data

Module `Langlands.BushnellKutzko.SplitTypeJacquet.LevelZeroTransport`. Let `F` be a
nonarchimedean local field, `L` an `𝔬_F`-lattice chain in `F^(m+1)` and `a` cuspidal layer data
for `L` (the Library's `LatticeChain.CuspidalLayerData`: bases of the layers and irreducible
cuspidal representations of the corresponding general linear groups over `k_F`). `unif F` is a
chosen uniformizer.

- `layerShape a` is the block shape whose blocks are the layer ranks in reversed order
  (`size i = a.rank (Fin.revPerm i)`); the ranks are positive because the layers are nonzero
  (`layerRank_pos`), and they sum to `m + 1` (`layerRank_sum`).
- `layerEquiv a` numbers the standard coordinates by the layers; reversing the order makes the
  layer order opposite to `blkOf (layerShape a)` (`layerEquiv_lt_iff`). `layerBasis a` is the
  adapted basis in this numbering and `layerChange a` the invertible matrix whose columns are its
  vectors. `toLin_layerChange_conj`: `toLin (g₀ x g₀⁻¹) = stdToAut x` for `g₀ = layerChange a`.
- `layerDatum a` is the Harish–Chandra datum with shape `layerShape a`, labelled by the classes of
  the layer factors in reversed order. `exists_blockLabel_ne`: if two layer factors have different
  classes (`factorClass`), then two blocks of `layerDatum a` have different labels.
- `layerTensorEquiv a` identifies the tensor product of the factor spaces with the Levi tensor of
  `layerDatum a`. It reindexes along the reversal and applies, in each factor, the equivalence
  `factorEquiv` with the chosen representative of its class.
- `layerReduction_eq_leviProjection`: for `x ∈ J0 F (blkOf (layerShape a))`, the reduction of
  `stdToAut x` on the layer `Fin.revPerm i` is the `i`-th block of the Levi projection of the
  reduction `redJ0 (layerShape a) x`. `layerTensorEquiv_inflation`: under `layerTensorEquiv a`, the
  inflation `a.inflation` of the layer factors at `stdToAut x` becomes `stdType (layerDatum a) x`,
  for every such `x`.
