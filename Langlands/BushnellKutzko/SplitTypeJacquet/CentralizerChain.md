# The centralizer chain over the valuation ring of `E`

Module `Langlands.BushnellKutzko.SplitTypeJacquet.CentralizerChain`.

Let `F` be a nonarchimedean local field and `E` an extension field acting on the
`F`-vector space `V` compatibly (`IsScalarTower F E V`). Let `𝓛` be an `𝔬_F`-lattice chain in `V`
whose stabilizer contains `E^×` (`hE`). Thus an element of `E^×` may shift the lattice indices.
`L_E = 𝓛.subfieldChain E hE` is the same chain as a
chain of modules over the integral closure `subfieldIntegers F E` of `𝔬_F` in `E`, which is
assumed to be a discrete valuation ring. In addition `E` carries a valuative relation, and
`φ : subfieldIntegers F E ≃+* 𝒪[E]` is a ring isomorphism with `(φ a : E) = (a : E)` (`hφ`). For a
finite extension of `F` with the Library's spectral valuation, `subfieldIntegerEquiv F E` is such
an isomorphism.

- `centralizerChain φ hφ 𝓛 hE` is the chain `L_E` viewed over `𝒪[E]` (`LatticeChain.transfer`);
  its lattices are those of `𝓛` (`mem_centralizerChain_lattice`, `coe_centralizerChain_lattice`).
- `layerTransfer`, `layerTransferInv` and `layerEquivE i : L_E.Layer i ≃+ C.Layer i` identify the
  layers `L_i / L_{i+1}` of the two chains, sending the class of `v ∈ L_i` to the class of `v`.
- `residueEquivE φ` is the isomorphism of residue fields induced by `φ`
  (`IsLocalRing.ResidueField.mapEquiv`), with `residueEquivE_residue`. `layerEquivE_smul` and
  `layerEquivE_symm_smul`: the layer isomorphism is semilinear for `residueEquivE φ`.
- `transportBasis i b`: a basis `b` of `L_E.Layer i` over the residue field of `𝔬_E` gives a basis
  of `C.Layer i` over `𝓀[E]`, with `transportBasis_apply` (its vectors are the images of those of
  `b`) and `transportBasis_repr` (its coordinates are the images of those of `b`).
- `centralizerChain_unitFiltration n`: `C.unitFiltration n = L_E.unitFiltration n`, since both are
  defined by the same lattice conditions (`mem_endFiltration_congr`).
  `centralizerChain_period`: the two chains have the same period
  (`PureApproximation.period_eq_of_coe_lattice_eq` with a uniformizer and its image under `φ`).
- `equivFun_toLin'`: the coordinates of `Matrix.GeneralLinearGroup.toLin' b A x` are
  `A.mulVec (b.equivFun x)`; `mulVec_equivFun_self`: `A.mulVec (b.equivFun (b s)) r = A r s`.
- `layerReduction_transfer`: let `b` be bases of the layers of `L_E` and `g ∈ L_E.unitFiltration 0`.
  For `i : Fin C.period`, the `(r, s)` entry of the reduction of `g` on the `i`-th layer of `C`, in
  the transported bases, is `residueEquivE φ` of the `(r, s)` entry of the reduction of `g` on the
  layer `Fin.cast _ i` of `L_E` in the bases `b` (`LatticeChain.layerReduction`). Proof: both
  reductions are determined by `layerReduction_spec` on the class of a lift of `b s`; the layer
  isomorphism carries one equation to the other, and coordinates in the transported basis are the
  images of coordinates in `b`.

Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
(1.2.1)–(1.2.4), printed pp. 24–25, describe the chain over the extension integers and
its endomorphism filtration. The change of integer-ring presentation here preserves the
underlying lattices and transports each quotient action by the induced residue-field map.
