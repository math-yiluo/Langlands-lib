# Surjectivity and kernel of the layer reduction of `U(𝔄)`

## Statements

Let `𝔬` be a discrete valuation ring with fraction field `K` and residue field `k`, let
`𝓛 = (L_j)_{j ∈ ℤ}` be an `𝔬`-lattice chain in a `K`-vector space `V` with period `e`, and let
`𝔄` be its hereditary order. For bases `b_i` over `k` of the layers `L_i / L_{i+1}`,
`0 ≤ i < e`, the map `LatticeChain.layerReduction b : U(𝔄) → ∏_{0 ≤ i < e} GL_{d_i}(k)` sends
`u` to the matrices of its actions on the layers (module
`Langlands.BushnellKutzko.LevelZeroSplitType`).

- `LatticeChain.layerReduction_surjective`: this map is surjective.
- `LatticeChain.layerReduction_eq_one_of_mem`: it sends every element of `U^1(𝔄)` to `1`.
- `LatticeChain.mem_unitFiltration_one_of_layerReduction_eq_one`: conversely, an element of
  `U(𝔄)` sent to `1` lies in `U^1(𝔄)`. So the kernel of the layer reduction is `U^1(𝔄)`.
- `LatticeChain.equivFun_layerReduction`: for `u ∈ U(𝔄)`, `0 ≤ i < e` and `v ∈ L_i`, the
  coordinate vector in the basis `b_i` of the class of `u v` in `L_i / L_{i+1}` is the
  `i`-th matrix of `layerReduction b u` applied to the coordinate vector of the class of `v`.
- `LatticeChain.layerReduction_apply_entry`: if the class of `v ∈ L_i` is the basis vector
  `b_i(y)`, then the `(x, y)` entry of the `i`-th matrix of `layerReduction b u` is the `x`-th
  coordinate of the class of `u v`.
- `LatticeChain.layerReduction_apply_eq_one`: if `u v - v ∈ L_{i+1}` for every `v ∈ L_i`,
  then the `i`-th matrix of `layerReduction b u` is `1`.
- `LatticeChain.exists_layer_linearEquiv`: for every `j ∈ ℤ` there is `0 ≤ s < e` with
  `L_s / L_{s+1} ≅ L_j / L_{j+1}` as `𝔬`-modules.
- `LatticeChain.exists_unitFiltration_layerAction`: a family `(Φ_i)_{i ∈ ℤ}` of
  `𝔬`-linear automorphisms of the layers `L_i / L_{i+1}` that commutes with the transport
  `L_i / L_{i+1} → L_{i+e} / L_{i+e+1}` by a uniformizer `ϖ` is the layer action of some
  `x ∈ 𝔄` that is a unit of `𝔄`.

## Source

Together these are the identification `U(𝔄) / U^1(𝔄) ≅ ∏_i GL(L_i / L_{i+1})` that Bushnell,
*Hereditary orders, Gauss sums and supercuspidal representations of GL_N* (1987), proof of
Theorem 2′(i), printed p. 197, reads off from the block matrix form (1.9) of `𝔄`, and that
Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), proof of
(8.1.5), printed p. 267, uses. The statements here are the surjectivity of the layer reduction and the
equality of its kernel with `U^1(𝔄)`.

## Proofs

*Lifting to a unit.* `LatticeChain.exists_order_lift_layers`
(`Langlands.BushnellKutzko.LatticeChainLayerLift`) lifts the family `Φ` to `x ∈ 𝔄` and the
inverse family `Φ⁻¹` to `x' ∈ 𝔄`. Then `x x'` and `x' x` act trivially on every layer
(`layerAction_eq_iff`), so `x x' - 1` and `x' x - 1` lie in `𝔓`, and `x x' = h₁`, `x' x = h₂`
for units `h₁, h₂ ∈ U^1(𝔄)` (`exists_mem_unitFiltration`). Hence `x` has the two-sided
inverse `x' h₁⁻¹ = h₂⁻¹ x'`, which lies in `𝔄`. This is the argument of
`LatticeChain.exists_unitFiltration_conj_sub_mem`
(`Langlands.BushnellKutzko.LatticeChainLayerIntertwining`), with the layer action of the
unit recorded in the conclusion.

*Surjectivity.* Given matrices `A_s ∈ GL_{d_s}(k)`, `0 ≤ s < e`, let `T_s` be the
automorphism of `L_s / L_{s+1}` with matrix `A_s` in the basis `b_s`. For `j ∈ ℤ` write
`j = s + e k` with `0 ≤ s < e` (`Int.ediv_emod_unique`) and set `Φ_j = σ_k T_s σ_k⁻¹`, where
`σ_k : L_s / L_{s+1} → L_j / L_{j+1}` is induced by `ϖ^k` (`stabilizerLayerEquiv` of the
`k`-th power of `uniformizerStabilizer`, whose shift is `k e`). Any presentation
`j = s + e k` gives the same `Φ_j`, and `σ_{k+1} = σ_ϖ ∘ σ_k`
(`stabilizerLayerEquiv_mul_apply`), so the family `Φ` commutes with the transport by `ϖ`. A
unit `u` with layer action `Φ` exists by the lifting lemma; for `0 ≤ s < e` the map `σ_0` is
the identity, so `u` acts on `L_s / L_{s+1}` by `T_s`, and `layerReduction_spec` gives
`layerReduction b u = A`.

*Coordinates.* `layerReduction_spec` says that the `i`-th matrix of `layerReduction b u`,
read as an endomorphism of `L_i / L_{i+1}` in the basis `b_i`
(`Matrix.GeneralLinearGroup.toLin'`), maps the class of `v` to the class of `u v`. Writing
the class of `v` as the linear combination of `b_i` with its coordinates and applying the
coordinate isomorphism `(b_i).equivFun` gives `equivFun_layerReduction`. Evaluating its
`x`-th component at the coordinate vector `Pi.single y 1` of `b_i(y)`
(`Matrix.mulVec_single_one`) gives `layerReduction_apply_entry`. For
`layerReduction_apply_eq_one`, the hypothesis says that `u` fixes every class in
`L_i / L_{i+1}` (`intervalMk_eq_iff`), so by `layerReduction_spec` the endomorphism attached to
the `i`-th matrix is the identity, and the matrix is `1` because
`Matrix.GeneralLinearGroup.toLin'` is injective.

*Layers of one period.* For `j ∈ ℤ` let `s = j mod e` and `k = ⌊j / e⌋`, so that
`j = s + e k` (`Int.emod_add_mul_ediv`). The isomorphism `L_s / L_{s+1} → L_j / L_{j+1}` of
`exists_layer_linearEquiv` is the map `σ_k` induced by `ϖ^k`, as in the proof of
surjectivity.

*Kernel.* If `g ∈ U^1(𝔄)` then `g v - v ∈ L_{i+1}` for `v ∈ L_i`, so
`layerReduction_apply_eq_one` gives `layerReduction b g = 1`.

Conversely, let `g ∈ U(𝔄)` with `layerReduction b g = 1`. By `layerReduction_spec`, `g` acts
trivially on `L_s / L_{s+1}` for `0 ≤ s < e`. The layer action of `g` commutes with the
transport by `ϖ` (`layerAction_commutes_uniformizer`), which maps `L_i / L_{i+1}` onto
`L_{i+e} / L_{i+e+1}`, so `g` acts trivially on `L_i / L_{i+1}` if and only if it acts
trivially on `L_{i+e} / L_{i+e+1}`. Induction on `k` in `i = (i mod e) + e k` shows that `g`
acts trivially on every layer. Then `g - 1 ∈ 𝔓` (`layerAction_eq_iff`), that is,
`g ∈ U^1(𝔄)`.
