# Layer sizes of principal lattice chains

The module `Langlands.BushnellKutzko.PrincipalChainResidueDegree` counts the successive quotients
of a lattice chain and deduces that the residue degree of a normalizing field divides the common
layer dimension of a principal chain.

## Declarations

For a lattice chain `𝓛 = (L_i)` over a commutative ring:

- `LatticeChain.natCard_interval_eq_relIndex`: the quotient `L_i/(L_i ∩ L_j)`
  (`LatticeChain.Interval`) has as many elements as the relative index
  `(L_j).toAddSubgroup.relIndex (L_i).toAddSubgroup` used in `LatticeChain.IsPrincipal`.
- `LatticeChain.relIndex_mul_relIndex_lattice`: relative indices multiply along `i ≤ j ≤ k`.
- `LatticeChain.relIndex_lattice_natCast_of_isPrincipal`: for a principal chain,
  `[L_0 : L_k] = [L_0 : L_1]^k` for `k ≥ 0`.

For a chain over `𝒪_F`, with `F` a nonarchimedean local field, `q = |k_F|` and `N = dim_F V`:

- `LatticeChain.natCard_interval_period`: `|L_0 / L_e| = q^N`, where `e` is the period.
- `LatticeChain.finrank_residueField_dvd_of_isPrincipal`: if the chain is principal and a field
  `E` acting on `V` has its units in `𝓛.stabilizer`, with `𝔬_E` a discrete valuation ring, finite
  over `𝒪_F`, and `algebraMap 𝒪_F 𝔬_E` local, then `[k_E : k_F]` divides `N / e`.

## Proofs

By periodicity `L_e = 𝔭_F L_0`, so `L_0/L_e` is `L_0 ⧸ 𝔭_F • ⊤`
(`Submodule.map_smul''`, `Submodule.comap_map_eq_of_injective`). This quotient is
`k_F ⊗_{𝒪_F} L_0` (`TensorProduct.quotTensorEquivQuotSMul`), of dimension
`rank_{𝒪_F} L_0 = N` over `k_F` (`Module.finrank_baseChange`; a basis of `L_0` is an `F`-basis
of `V` by `Module.Basis.extendOfIsLattice`), so it has `q^N` elements.

For the divisibility, a principal chain gives `[L_0 : L_1]^e = [L_0 : L_e] = q^N`. The layer
`L_0/L_1` is a vector space over `k_E` (`LatticeChain.subfieldLayerResidueModule`), finite since
it is finite-dimensional over the finite field `k_F`, so `|L_0/L_1| = |k_E|^m` with
`m = dim_{k_E}(L_0/L_1)`, and `|k_E| = q^f` with `f = [k_E : k_F]`
(`Module.natCard_eq_pow_finrank`). Comparing exponents of `q > 1` gives `N = f m e`, so
`N / e = f m`.

## Source

Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994), printed p. 110
(PDF p. 123): the layer dimensions `d_i(𝔄) = dim_{k_F}(L_i/L_{i+1})` with
`Σ_{i=0}^{e−1} d_i = N`; for a principal order they are all `N / e`. The divisibility is the
argument on printed p. 113 (PDF p. 126): each `L_i/L_{i+1}` is a `k_{F[α]}`-vector space, so
`deg f_α` divides `d(𝔄)`. Source `bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
