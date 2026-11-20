# Ramification index from `𝔅 + 𝔓`

Helper module for the proof of `Langlands.BushnellKutzko.StratumEquivalenceStatement`,
covering the ramification-index half of Bushnell–Kutzko 1993, (2.1.4)(iii), printed p. 50.
The setting is a finite field extension `E/F` acting on `V` compatibly with `F`, with `E^×`
normalizing the `𝔬_F`-lattice chain `𝓛 = (L_i)` (hypothesis `hE`), and filtration
`𝔓^n = 𝓛.endFiltration n`.

**Definitions.**
- `fieldCommutant E`: the `𝔬_F`-submodule of `F`-endomorphisms commuting with the action of
  `E`, i.e. `End_E(V)`.
- `fieldOrder 𝓛 E = 𝔓^0 ∩ End_E(V)`, the order `𝔅_E = 𝔄 ∩ End_E(V)`.
- `LayerNull 𝓛 x j`: `x L_j ⊆ L_{j+1}`.
- `IsLayerPeriod 𝓛 M d`: for every `j` and every `x ∈ M`, `LayerNull x j ⟺ LayerNull x (j+d)`.
  This depends only on `𝓛` and `M`.

**Lemmas.**
- `layerNull_add_iff`: adding an element of `𝔓^1` does not change `LayerNull`.
- `layerNull_iff_of_commute`: for `x ∈ End_E(V)` and `a ∈ E^×`,
  `LayerNull x j ⟺ LayerNull x (j + shift a)`, because `a L_j = L_{j + shift a}` and `x`
  commutes with `a` (`shift` is from `StratumEquivalenceShift`).
- `rankOne F w k c y`: for an `E`-basis `w`, the map `v ↦ w_k^*(v) c⁻¹ y` (`E`-linear,
  viewed as an `F`-endomorphism; in Lean `c⁻¹` is `0` when `c = 0`, so `rankOne F w k 0 y`
  is the zero map). `rankOne_apply_basis`: for `c ≠ 0` it sends `c w_k` to `y`.
- `rankOne_mem_fieldOrder`: if `w` is a splitting basis (`StratumEquivalenceSplitting`),
  `c w_k` has exact depth `0` and `y ∈ L_0`, the map lies in `𝔅_E`. Exact depth forces
  `c w_k ≠ 0`, so `c ≠ 0`. Let `v ∈ L_i` and `s = w_k^*(v) c⁻¹`, so the map sends `v` to
  `s y`. If `s = 0`, then `s y = 0 ∈ L_i`. If `s ≠ 0`, the vector
  `s · (c w_k) = w_k^*(v) w_k` lies in `L_i` (`coord_smul_mem`) and has exact depth
  `shift s` (`ExactDepth.smul`), so `shift s ≥ i` and `s y ∈ L_i` (`smul_mem_of_shift_le`).
- `exists_basis_depth_zero` (`F` a nonarchimedean local field, `dim_F V < ∞`): a splitting
  basis with some `c w_k` of exact depth `0` exists (`exists_relative_splitting_basis`,
  `exists_scaled_basis_at_depth`).

**Main results** (`F` a nonarchimedean local field, `V` finite-dimensional).
- `isLayerPeriod_iff`: the layer periods of `M = 𝔅_E + 𝔓` are exactly the shifts of the
  elements of `E^×`.
  *Shifts are periods*: write `x = b + p` with `b ∈ 𝔅_E`, `p ∈ 𝔓`; drop `p` by
  `layerNull_add_iff` and apply `layerNull_iff_of_commute` to `b`.
  *Periods are shifts*: let `u = c w_k` have exact depth `0` (so `c ≠ 0`) and `p` the
  rank-one map `v ↦ w_k^*(v) c⁻¹ u ∈ 𝔅_E`. Then `p u = u ∉ L_1`, so `p` is not layer-null at
  `0`, hence not at `d`: some `v ∈ L_d` has `p v = t w_k ∉ L_{d+1}`, where `t = w_k^*(v)`.
  Since `t w_k ∈ L_d` by the splitting property, `t w_k = a u` with `a = t c⁻¹` has exact
  depth `d`. Here `a ≠ 0`, since `a u ∉ L_{d+1}` while `0 ∈ L_{d+1}`. So `a u` also has exact
  depth `0 + shift a`, and `d = shift a`.
- `exists_shift_eq_mul`, `isLayerPeriod_iff_dvd`: the shifts are exactly the multiples of
  `e' = shift ϖ_E` (`shift_uniformizer_dvd`, powers of `ϖ_E` and their inverses).
- `shift_uniformizer_eq_of_sup_eq`: two normalizing fields `E`, `E'` with the same
  `𝔅 + 𝔓` have the same set of layer periods, so `e'_E ∣ e'_{E'}` and `e'_{E'} ∣ e'_E`; both
  are positive, hence equal.
- `ramificationIndex_eq_of_sup_eq`: by `ramificationIndex_mul_shift`,
  `e(E|F) · e'_E = e(𝓛) = e(E'|F) · e'_{E'}`; cancel the common positive `e'`.

BK93 derives (2.1.4)(iii) from the structure of `𝔅/𝔔` as a product of matrix algebras over
the residue field of `E` (Wedderburn theory). The argument here is different: it recovers
`e(E|F)` from the periodicity of the layer-null condition on `𝔅 + 𝔓`, which avoids
identifying `𝔅` as a hereditary order of `End_E(V)`.
