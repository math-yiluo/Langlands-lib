# The period of a principal lattice chain divides the dimension

`Langlands.BushnellKutzko.SimpleStratumLabel.period_dvd_finrank_of_isPrincipal`:
for a nonarchimedean local field `K` and a principal `𝒪[K]`-lattice chain
`L` in a finite-dimensional `K`-vector space `V`, the period `e(L)`
divides `N = dim_K V`. Equivalently `N = e(L) d` with `d` the common
dimension over the residue field of the layers `L_i/L_{i+1}`
(Bushnell–Kutzko 1994, `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
printed p. 110: the layer dimensions have sum `N` over a period).

## Proof

- `relIndex_eq_natCard_quotient`: the index `(N₀ : N₁)` of additive
  subgroups is the cardinality of the module quotient.
- `exists_relIndex_eq_pow`: if `𝔭 N₀ ⊆ N₁ ⊆ N₀` and `N₀` is finitely
  generated, the quotient is a finite vector space over the residue field
  (`Module.IsTorsionBySet.module`), so `(N₀ : N₁)` is a power of `q`.
- `relIndex_maximalIdeal_smul`: for a lattice `N₀`, `(N₀ : 𝔭 N₀) = q^N`,
  since `N₀/𝔭N₀` has dimension `spanFinrank N₀ = rank N₀ = N`
  (`IsLocalRing.spanFinrank_eq_finrank_quotient`,
  `Submodule.IsLattice.rank'`).

For a principal chain all layer indices equal `c = (L_0 : L_1)`, so
`(L_0 : L_e) = c^e` by multiplicativity of indices. Since
`L_e = 𝔭 L_0`, this is `q^N`; and `c = q^a` by the second item. Hence
`a e = N`.
