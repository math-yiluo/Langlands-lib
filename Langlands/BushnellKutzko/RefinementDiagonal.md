# Relative splitting bases and the attached diagonal embedding

Internal helper module for the proof of BK93 (2.2.8) (`RefinementProof`). `L` is a field
acting on `V` (`IsScalarTower F L V`) whose units normalize the lattice chain `𝓛` over `𝒪[F]`.

## Relative splitting bases (as in BK93 (1.2.8))

- `refinement_scalar_lattice_shift`: a nonzero `c ∈ L` shifts the chain by a fixed integer.
- `refinement_lattice_maximal_coset_rep`: a coset `x + U` of an `L`-subspace that avoids zero
  has a representative lying in every lattice that meets the coset.
- `refinement_coset_rep_smul_mem`: for such a representative `w`, if `u + c w ∈ L_i` with
  `u ∈ U`, then `c w ∈ L_i`.
- `RelSplits 𝓛 w` (internal definition): whenever `Σ c_j w_j ∈ L_i`, every term `c_j w_j` lies
  in `L_i`.
- `relSplits_finCons` and `exists_relSplits_basis`: a maximal splitting family is an `L`-basis,
  so a relative splitting basis exists.

These four lemmas and the construction re-prove, under public names, the private lemmas
`exists_scalar_lattice_shift`, `exists_lattice_maximal_coset_rep`,
`coset_rep_smul_mem_of_add_mem`, `relativeSplits_finCons` and `exists_relative_splitting_basis`
of the Library module `RelativeFiltrationInversion`, which cannot be imported. The arguments
follow those private proofs.

## Matrix units and the diagonal embedding

For an `L`-basis `w` of `V` (indexed by `Fin n`):

- `lineIncl`, `lineProj`: the inclusion `a ↦ a w_j` and the coordinate `v ↦ w.repr v j`.
- `matUnit j l = ε_{jl}`: `Σ c_i w_i ↦ c_l w_j`, with `ε_{jl} ε_{km} = δ_{lk} ε_{jm}` and
  `Σ_j ε_{jj} = 1`.
- `diagonal : End_F(L) →ₐ[F] End_F(V)`, `Δ(y)(Σ c_j w_j) = Σ y(c_j) w_j` (built from
  `diagonalLinear`). It commutes with the matrix units and sends `mulLeft a` to the action of
  `a`. It is injective (`diagonal_injective`).
- `compress l z = π_l ∘ z ∘ ι_l`. `diagonal_compress` says `Δ(compress l z)` is the sandwich
  `σ_l(z) = Σ_j ε_{jl} z ε_{lj}`. It recovers `z` if `z` commutes with every `ε_{jk}`
  (`diagonal_compress_of_commute`). For `L`-linear `z` it is multiplication by the `(l, l)`
  entry (`compress_of_commute`).

## Filtration properties (for a relative splitting basis)

- `repr_smul_mem`: if `v ∈ L_i`, each term `w.repr v j • w_j` lies in `L_i`.
- `matUnit_self_mem`: `ε_{jj} ∈ 𝔄`.
- `smul_mem_lattice_index_shift` and `subfieldEmbedding_mem_iff`: the action of `a ∈ L` lies in
  `𝔓^k` iff `a v ∈ L_{ν(v)+k}` for one (any) nonzero `v`.
- `matUnit_sandwich_mem` and `diagonal_compress_mem`: `ε_{jl} z ε_{lj}` and `σ_l(z)` preserve
  each `𝔓^s`.
- `block_mem` and `sum_blocks`: `z = Σ_{j,l} ε_{jj} z ε_{ll}`, with every block in `𝔓^s` when
  `z ∈ 𝔓^s`.
