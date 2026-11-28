# Inserting one lattice into a lattice chain

## Statement

Let `𝓛 = (L_j)_{j ∈ ℤ}` be an `𝔬_F`-lattice chain in `F^ι` with period `e(𝓛)`, let
`p ∈ ℤ`, and let `M` be an `𝔬_F`-lattice with `L_{p+1} ⊊ M ⊊ L_p`.
`LatticeChain.exists_insertLattice` gives a lattice chain `𝓜` with `e(𝓛) < e(𝓜)` such
that every `g ∈ U^1(𝓜)`

- lies in `U(𝓛) = U^0(𝓛)`;
- satisfies `(g - 1) L_j ⊆ L_{j+1}` for every `j ≠ p` with `p - e(𝓛) < j < p + e(𝓛)`;
- satisfies `(g - 1) L_p ⊆ M` and `(g - 1) M ⊆ L_{p+1}`.

The lattices of `𝓜` are the `L_j` together with the `ϖ^k M`, `k ∈ ℤ`.

## Source

This is the refinement step in the proof of Bushnell–Kutzko, *The admissible dual of GL(N)
via compact open subgroups* (1993), (8.1.5), printed p. 268 (PDF p. 280), which repeats the
argument of Bushnell, *Hereditary orders, Gauss sums and supercuspidal representations of
GL_N* (1987), proof of Theorem 2′(i), printed p. 197 (PDF p. 14): the inverse image in
`U(𝔄)` of a proper parabolic subgroup of `U(𝔄)/U^1(𝔄)` is `U(𝔅)` for a hereditary order
`𝔅 ⊂ 𝔄` with `e(𝔅) > e(𝔄)`. The statement here records only what that argument uses: the inclusion of
`U^1(𝔅)` in `U(𝔄)` and the action of `U^1(𝔅)` on the layers of `𝓛`.

## Proof

Fix a uniformizer `ϖ` and let `C` be the set of lattices `L_j` (`j ∈ ℤ`) and `ϖ^k M`
(`k ∈ ℤ`). Each member of `C` lies between two consecutive members of `𝓛`
(`LatticeChain.IsSandwiched`, from `Langlands.BushnellKutzko.MoyReduction`), so `C` is
totally ordered by inclusion, is stable under multiplication by `ϖ^{±1}`, satisfies
`ϖ N ⊊ N`, and has finitely many members between any two of its members. The theorem
`exists_latticeChain_range_eq` of `MoyReduction` then gives a lattice chain `𝓜` whose
range is `C`.

Write `L_j = M_{σ(j)}`. Since `ϖ^k M` lies strictly between `L_{p+ek+1}` and `L_{p+ek}`,
no member of `C` lies strictly between `L_{j+1}` and `L_j` for `j ≢ p`, nor between `M`
and `L_p`, nor between `L_{p+1}` and `M`. Hence `M_{σ(j)+1} = L_{j+1}` for those `j`, and
`M_{σ(p)+1} = M`, `M_{σ(p)+2} = L_{p+1}`. The map `σ` is strictly increasing with
`σ(p + e(𝓛)) = σ(p) + e(𝓜)`; since `σ(p+1) = σ(p) + 2`, this gives `e(𝓜) > e(𝓛)`.

An element `g ∈ U^1(𝓜)` satisfies `(g - 1) M_t ⊆ M_{t+1}` for every `t`, and
`g^{±1} M_t ⊆ M_t`. Applied at `t = σ(j)`, `σ(p)` and `σ(p) + 1`, these give the
three properties.
