# Refining a lattice chain at a non-cuspidal layer

## Statement

Let `F` be a nonarchimedean local field with residue field `k`, let `𝓛 = (L_j)_{j ∈ ℤ}` be an
`𝔬_F`-lattice chain in `F^ι` of period `e`, with hereditary order `𝔄`, and choose bases
`b_i` over `k` of the layers `L_i / L_{i+1}`, `0 ≤ i < e`, of dimensions `d_i`. Let
`φ = LatticeChain.layerReduction b : U(𝔄) → ∏_{0 ≤ i < e} GL_{d_i}(k)` be the layer
reduction (module `Langlands.BushnellKutzko.LevelZeroSplitType`).

Let `τ` be a complex representation of `Aut_F(F^ι)` on `W`, let `ρ_i` be complex
representations of `GL_{d_i}(k)` on nonzero spaces `Y_i`, and let `f : ⊗_i Y_i → W` be an
injective linear map with

`f((⊗_i ρ_i)(φ(g)) x) = τ(g) f(x)` for all `g ∈ U(𝔄)` and `x ∈ ⊗_i Y_i`,

where `⊗_i ρ_i` is the external tensor product `FiniteTensor.external ρ`.

`LatticeChain.exists_refinement_of_not_isCuspidal`: if some `ρ_{i₀}` is not cuspidal
(`FiniteGeneralLinear.IsCuspidal`), there is a lattice chain `𝓜` in `F^ι` with
`e(𝓛) < e(𝓜)` and a nonzero `w ∈ W` with `τ(g) w = w` for every `g ∈ U^1(𝓜)`.

`tprod_ne_zero_of_forall_ne_zero`: a pure tensor `⊗_i v_i` of nonzero vectors `v_i` of
complex vector spaces, indexed by a finite type, is nonzero.

## Source

This is the refinement step in the proof of Bushnell–Kutzko, *The admissible dual of GL(N)
via compact open subgroups* (1993), (8.1.5), printed p. 268 (PDF p. 280), which follows
Bushnell, *Hereditary orders, Gauss sums and supercuspidal representations of GL_N* (1987),
proof of Theorem 2′(i), printed p. 197 (PDF p. 14). There an irreducible factor `ϑ` of the
restriction of `π` to `U(𝔄)` that is trivial on `U^1(𝔄)`, viewed as a representation of
`U(𝔄)/U^1(𝔄)`, is cuspidal unless its restriction to some proper parabolic subgroup has a
vector fixed by the unipotent radical, and the preimage of that parabolic subgroup is
`U(𝔅)` for a hereditary order `𝔅` with `e(𝔅) > e(𝔄)`, so that `π` has a nonzero vector
fixed by `U^1(𝔅)`. The statement here uses only that `U^1(𝔅)` maps into the unipotent
radical, not that the preimage of the parabolic subgroup is `U(𝔅)`.

## Proof

*A proper parabolic and its stable subspace.* Since `ρ_{i₀}` is not cuspidal, there are a
block shape `B` of `d_{i₀}` whose standard parabolic subgroup `P_B` is proper and a nonzero
`z₀ ∈ Y_{i₀}` fixed by the unipotent radical `U_B`. Because `P_B` is proper, some
coordinate `x₀` lies in a strictly later block than some coordinate `y₀`
(`GeneralLinear.BlockShape.mem_parabolic_iff`). Let `S ⊆ L_{i₀} / L_{i₀+1}` be the
`k`-span of the basis vectors `b_{i₀}(x)` whose block is at most that of `y₀`, and let
`M ⊆ L_{i₀}` be its preimage. Then `L_{i₀+1} ⊊ M` because `b_{i₀}(y₀) ∈ S` is nonzero, and
`M ⊊ L_{i₀}` because `b_{i₀}(x₀) ∉ S` (`Module.Basis.mem_span_image`).

*The finer chain.* `LatticeChain.exists_insertLattice`
(`Langlands.BushnellKutzko.LatticeChainInsertion`) gives a lattice chain `𝓜` of larger
period such that every `g ∈ U^1(𝓜)` lies in `U(𝔄)`, acts trivially on `L_i / L_{i+1}` for
`0 ≤ i < e`, `i ≠ i₀`, and satisfies `(g - 1) L_{i₀} ⊆ M` and `(g - 1) M ⊆ L_{i₀+1}`.

*The image of `U^1(𝓜)`.* Let `g ∈ U^1(𝓜)`. For `i ≠ i₀` the `i`-th component of `φ(g)` is
`1` (`LatticeChain.layerReduction_apply_eq_one`). For the `i₀`-th component, lift
`b_{i₀}(c)` to `v ∈ L_{i₀}`; by `LatticeChain.layerReduction_apply_entry` its `(a, c)`
entry is the `a`-th coordinate of the class of `g v = v + (g - 1) v`, that is `δ_{ac}` plus
the `a`-th coordinate of the class of `(g - 1) v`. Suppose the block of `c` is at most the
block of `a`. If the block of `c` is at most that of `y₀`, then `v ∈ M` and
`(g - 1) v ∈ L_{i₀+1}` has class `0`. Otherwise neither `c` nor `a` has block at most that
of `y₀`, and the class of `(g - 1) v ∈ M` lies in `S`, so its `a`-th coordinate vanishes.
So the entries of the `i₀`-th component in the blocks on and below the diagonal are those of
the identity, and the component lies in `U_B` (`GeneralLinear.BlockShape.mem_unipotentSubgroup_iff`).

*The fixed vector.* Choose nonzero `z_i ∈ Y_i` with `z_{i₀} = z₀`. By the previous step
`(⊗_i ρ_i)(φ(g))` fixes `⊗_i z_i` for `g ∈ U^1(𝓜)` (`FiniteTensor.external_tprod`), so
`w = f(⊗_i z_i)` is fixed by `τ(g)`. The pure tensor `⊗_i z_i` is nonzero
(`tprod_ne_zero_of_forall_ne_zero`): in the tensor product basis built from bases of the
`Y_i` (`Basis.piTensorProduct`) one of its coordinates is a product of nonzero coordinates of
the `z_i`. As `f` is injective, `w ≠ 0`.
