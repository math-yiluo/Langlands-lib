# Layer actions and families transported along a translation

Module `Langlands.BushnellKutzko.NonsplitFundamentalSimpleLayers`, namespace
`Langlands.BushnellKutzko.NonsplitSimple`. It imports `NonsplitFundamentalSimpleStatement`,
`LatticeChainLayerCommutation` (which imports the layer modules `LatticeChainLayers` and
`LatticeChainLayerLift`), `CriticalDerivedNormalization` and
`NonsplitFundamentalSimpleAlgebra`.

## Setting

`O` is a commutative ring with an algebra map to a field `K`, `V` is a `K`-vector space and
`𝓛 = (L_i)` is an `O`-lattice chain in `V`. Write `𝔄 = 𝓛.order`, `𝔓^j = 𝓛.endFiltration j`
and `𝔓 = 𝓛.firstFiltrationIdeal`. The layer `L_i/L_{i+1}` is `𝓛.Layer i`, and a translation is
an element of `𝓛.stabilizer`, a unit `t` with `t L_i = L_{i+s}` for its shift
`s = 𝓛.stabilizerValuation t`. `𝓛.stabilizerLayerEquiv t i j` is the map
`L_i/L_{i+1} → L_j/L_{j+1}` induced by `t` when `j = i + s`.

## The action of `𝔄/𝔓` on the layers

- `layerHom 𝓛 i : 𝔄 →ₐ[O] End_O(L_i/L_{i+1})` is the Library's `𝓛.layerAction`, as an algebra
  homomorphism.
- `layerAction_eq_zero_iff`: `x ∈ 𝔄` acts by zero on every layer exactly when `x ∈ 𝔓`. This is
  `LatticeChain.layerAction_eq_iff` with the second element zero.
- `residueLayerHom 𝓛 i : 𝔄/𝔓 →+* End_O(L_i/L_{i+1})` is the induced homomorphism.

## Translations

- `stabilizerValuation_zpow`: the shift of `t^n` is `n` times the shift of `t`.
- `mem_order_of_shift_zero` and `stabilizerLayerEquiv_eq_layerAction`: a translation of shift
  zero lies in `𝔄`, and on each layer its layer map is its action as an element of `𝔄`.
- `stabilizerLayerEquiv_congr`: the layer map depends only on the translation, not on the proof
  of the index equation.

## Extending families along a translation

Fix a translation `t` of shift `g > 0`. Every integer is `i = (i mod g) + g ⌊i/g⌋`, so `t^{⌊i/g⌋}`
carries the layer at `i mod g` onto the layer at `i` (`index_eq`).

- `conjLayer` transports an endomorphism of one layer to another by conjugation with a layer
  map, and `conjLayer_congr` shows that the result depends only on the indices and the
  translation.
- `extendFamily 𝓛 t ht c` sends `i` to the transport of `c (i mod g)` along `t^{⌊i/g⌋}`.
- `extendFamily_of_mem`: at `0 ≤ r < g` the family is `c r`.
- `extendFamily_commutes`: the family commutes with `t` in the sense of
  `LatticeChain.LayerFamilyCommutes`. The proof writes `t^{⌊(i+g)/g⌋} = t · t^{⌊i/g⌋}` and
  composes layer maps with `LatticeChain.stabilizerLayerEquiv_mul_apply`.
- `extendFamily_commutes_of_commute`: if `z` is a translation of shift zero commuting with `t`
  and every `c r`, `0 ≤ r < g`, commutes with the layer map of `z`, then the family commutes with
  `z`. Since `z t^q = t^q z`, the layer map of `z` at `i` is the transport of the one at
  `i mod g`.
- `eq_zero_of_commutes`: a family commuting with `t` that vanishes at `0 ≤ r < g` vanishes. The
  translations commuting with a family form a subgroup
  (`LatticeChain.layerCommutingSubgroup`), which contains `t^{⌊i/g⌋}`, and its layer map is
  bijective.

## Provenance

These constructions are a coordinate-free replacement for the block-matrix description of
hereditary orders in Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (2.5.1)–(2.5.5), printed pp. 76–79 (PDF pp. 88–91), literature ID
`bushnell-kutzko-1993-admissible-dual-gln`: there `𝔄/𝔓` is a product of matrix algebras over
the residue field, one for each layer in a period, and `b` permutes the blocks cyclically. They
are used for (2.4.13) in `NonsplitFundamentalSimpleResidue`.
