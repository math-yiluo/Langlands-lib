# Periods and conjugacy of principal orders

The module `Langlands.BushnellKutzko.PrincipalOrderConjugacy` proves three facts about
`𝒪_F`-lattice chains `𝓛 = (L_i)` in a finite-dimensional vector space `V` of dimension
`N` over a nonarchimedean local field `F`, with `e(𝓛)` the period (`LatticeChain.period`).

## Declarations

- `LatticeChain.algebraMap_uniformizer_mem_endFiltration_iff`: for a uniformizer `ϖ`,
  multiplication by `ϖ` lies in `End^n(𝓛)` (`LatticeChain.endFiltration n`) exactly when
  `n ≤ e(𝓛)`.
- `LatticeChain.period_eq_of_order_eq`: two chains with the same order `𝔄(𝓛)` have the same
  period.
- `LatticeChain.period_dvd_finrank_of_isPrincipal`: the period of a principal chain
  (`LatticeChain.IsPrincipal`) divides `N`.
- `LatticeChain.period_dvd_finrank_of_isPrincipalOrder`: the period of any chain whose order
  satisfies `IsPrincipalOrder` divides `N`.
- `LatticeChain.mem_lattice_iff_of_splits`: for a basis splitting `𝓛`
  (`LatticeChain.Splits`), a vector lies in `L_i` exactly when each of its basis terms does.
- `LatticeChain.smul_mem_lattice_iff_index` gives the coefficient bound for `x ≠ 0`.
  Then `c • x ∈ L_j` holds exactly when `c = 0` or `j ≤ ν(x) + e(𝓛) ord(c)`, where
  `ν = LatticeChain.index` and `ord = ordOf`.
- `LatticeChain.residue_eq_zero_iff_one_le_ordOf`: a nonzero integral element has zero
  residue exactly when its order is at least one.
- `LatticeChain.exists_basis_splits_index_lt`: every chain has a splitting basis whose
  vectors have indices in `[0, e)`.
- `LatticeChain.natCard_layer_of_splits`: for such a basis and `0 ≤ s < e`, the layer
  `L_s / L_{s+1}` (`LatticeChain.Layer s`) has `q^{n_s}` elements, where `q = |k_F|` and
  `n_s` is the number of basis vectors of index `s`.
- `LatticeChain.card_index_eq_of_isPrincipal`: for a principal chain, `n_s · e = N` for every
  `0 ≤ s < e`.
- `LatticeChain.exists_linearEquiv_corresponds_of_isPrincipal`: two principal chains of the
  same period correspond under a linear automorphism `f` of `V`, in the sense of
  `LatticeChain.Corresponds` (`v ∈ L_i ↔ f v ∈ L'_i` for all `i`).
- `LatticeChain.exists_order_eq_of_isPrincipalOrder`: if the orders of `L₁` and `L₂` are
  principal and `e(L₁) = e(L₂)`, there is `g ∈ Aut_F(V)` with
  `(L₁.linearEquivMap g).order = L₂.order`.

## Proofs

**Period and order.** For `v ∈ L_0 \ L_1`, `ϖv ∈ L_{e} \ L_{e+1}`
(`LatticeChain.uniformizer_smul_mem_iff`), which gives the characterization of the steps of
`End^n(𝓛)` containing `ϖ`. Chains with the same order have the same filtration `End^n`
(`LatticeChain.endFiltration_eq_of_order_eq`, module `SimpleCharacterSequence`), so their
periods agree.

**Divisibility.** For a principal chain `[L_0 : L_1]^e = [L_0 : L_e] = q^N`
(`LatticeChain.relIndex_lattice_natCast_of_isPrincipal` and
`LatticeChain.natCard_interval_period`, module `PrincipalChainResidueDegree`). The layer
`L_0/L_1` is a finite `k_F`-vector space, so `[L_0 : L_1] = q^d` with `d` its dimension
(`Module.natCard_eq_pow_finrank`), and `de = N`. For a chain whose order is principal, the
principal chain with the same order has the same period.

**Conjugacy.** `LatticeChain.exists_basis_splits` (module `SplittingBasis`) gives a basis
splitting the chain. Multiplying each basis vector by a power of `ϖ` moves its index into
`[0, e)` (`LatticeChain.index_smul`). For `0 ≤ s < e`, the coefficients at basis vectors of
index `s` of a vector in `L_s` are integral. Reducing them modulo `𝔭_F` gives an
`𝒪_F`-linear surjection `L_s → k_F^{n_s}`, since each residue coordinate can be lifted to
an integral coefficient at a basis vector of index `s`.

The kernel is `L_{s+1}` by checking the basis terms. A zero coefficient gives the zero
term, which lies in `L_{s+1}`. For `c ≠ 0`, `ν(cβ_k) ≡ ν(β_k) (mod e)`. If `ν(β_k) ≠ s`,
the indices `ν(β_k)` and `s` are distinct in `[0, e)`, so `ν(cβ_k) ≠ s`. Membership in
`L_s` then forces `ν(cβ_k) ≥ s+1`. If `ν(β_k) = s` and `c ≠ 0`, membership in `L_{s+1}` is
equivalent to `ord(c) ≥ 1`, which is equivalent to `c` having zero residue.

Thus `|L_s/L_{s+1}| = q^{n_s}`. For a principal chain all these cardinalities are equal, so
all `n_s` are equal, and summing over the fibres of the index map gives `n_s e = N`. Two
principal chains of the same period therefore have index maps on their bases with fibres of
the same size, and an equivalence of the index sets preserving indices
(`Equiv.ofFiberEquiv`) defines a basis change `f` (`Module.Basis.equiv`). Membership of a
basis term in a lattice depends only on its coefficient, the index of the basis vector and
the period, so `f` carries every `L_i` onto `L'_i`. For orders, pass to the principal chains
with the same orders, which have the same periods, and use
`LatticeChain.Corresponds.order_eq_iff`.

## Sources

Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
§1.1, printed pp. 22–23 (PDF pp. 34–35): the lattice-chain bases (1.1.7), in which a
hereditary order is block upper triangular modulo `𝔭_F`. Literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994), printed
p. 126 (PDF p. 139), before (3.8): a principal order is determined up to conjugacy by its
period, which can be any positive divisor of `N`. Literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
The module proves the divisibility and the conjugacy; it does not prove that every divisor
occurs. The proofs follow the splitting-basis route above rather than a printed proof.
