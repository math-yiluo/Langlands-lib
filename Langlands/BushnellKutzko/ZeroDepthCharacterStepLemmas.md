# The groups `J(β, 𝔄) ⊇ J^1(β, 𝔄)` of a simple stratum of level zero

This internal module records group-theoretic and topological facts about the groups
`J^m(β, 𝔄)` (`simpleJGroup`) and `J(β, 𝔄)` (`simpleJ`) of Bushnell–Kutzko, *The admissible dual
of GL(N) via compact open subgroups* (BK93), §3.1, as used in the proof of (8.1.5), printed
pp. 268–269. There `[𝔄, n, 0, β]` is a simple stratum, `θ` a simple character of `H^1(β, 𝔄)`, and
an irreducible smooth representation `π` containing `θ` is analysed through the finite group
`J(β, 𝔄) / J^1(β, 𝔄) ≅ U(𝔅_β) / U^1(𝔅_β)`.

## Groups

The statements in this section hold for a lattice chain `L` over any commutative ring `O` with
an `O`-algebra `F` that is a field.

- `relativeUnitFiltration_le_simpleJGroup`: `U^m(𝔅_β) = U^m(𝔄) ∩ B_β^×`
  (`relativeUnitFiltration L β m`) lies in `J^m(β, 𝔄)`. An element `g` of `U^m(𝔅_β)` commutes
  with `β`, so `g` lies in the centralizer lattice `𝔄 ∩ B_β` (`centralizerLattice L β 0`), which
  is the first summand of `𝔍(β, 𝔄)`; with `g ∈ U^m(𝔄)` this places `g` among the generators of
  `J^m(β, 𝔄)`.
- `exists_endFiltration_le_simpleJLattice'`: some step `𝔓^t` of the filtration of `A = End_F(V)`
  lies in `𝔍(β, 𝔄)` (`simpleJLattice`). By induction on the defining sequence: for a minimal
  element the lattice has `𝔓^{⌊(n+1)/2⌋}` (`simpleJCutoff n`) as a summand, and in the inductive
  step `𝔍` contains the intersection of the lattice of the next element with
  `𝔓^{simpleJCutoff k}` for the critical depth `k`, so the larger of the two exponents works.
- `one_mem_simpleJLattice'`: the identity lies in `𝔍(β, 𝔄)`, since it lies in `𝔄 ∩ B_β`.
- `exists_unitFiltration_le_simpleJGroup`: some `U^k(𝔄)` lies in `J^m(β, 𝔄)`. With `𝔓^t` as
  above, take `k = max(m, t)`: an element `g ∈ U^k(𝔄)` lies in `U^m(𝔄)`, and
  `g = (g - 1) + 1 ∈ 𝔓^t + 𝔍(β, 𝔄) ⊆ 𝔍(β, 𝔄)`.

## Simple strata of level zero

Here `F` is a nonarchimedean local field, `V` an `F`-vector space, and `S` a simple stratum with
`S.r = 0`, with a chosen defining sequence `q`.

- `simpleJGroup_one_subgroupOf_normal`: `J^1(β, 𝔄)` is normal in `J(β, 𝔄)`. The carrier of
  `J(β, 𝔄)` is the set of units in `𝔍(β, 𝔄)` (`simpleStratumGroupProperties`, part 1 at `m = 0`).
  For `h ∈ J^1` and `j ∈ J`, the conjugate `j h j⁻¹` lies in `𝔍(β, 𝔄)` because it lies in `J`, and
  in `U^1(𝔄)` because `U^1(𝔄)` is normalized by `U^0(𝔄) ⊇ J`
  (`LatticeChain.inv_mul_mul_mem_unitFiltration`); so it is a generator of `J^1(β, 𝔄)`.
- `exists_relativeUnit_mul_simpleJGroup_one`: every `d ∈ J(β, 𝔄)` is a product `u k` with
  `u ∈ U(𝔅_β)` and `k ∈ J^1(β, 𝔄)`, that is, `J(β, 𝔄) = U(𝔅_β) J^1(β, 𝔄)` (compare BK93 (3.1.15), printed p. 95). This
  is `simpleJ_intertwiningDomain_product` at the identity element `y = 1` of `B_β^×`: the domain
  `J ∩ 1 J 1⁻¹` is `J` itself.

## Topology

Here `F` is a nonarchimedean local field and `A = End_F(F^n)` carries its module topology.

- `exists_unitFiltration_subset_nhds_aut`: every neighbourhood of the identity of `A^×` contains
  some `U^m(𝔄)`. The groups `U^m(𝔄)` form a decreasing sequence of compact open subgroups of
  `A^×` whose intersection is `{1}`: an element `g` of every `U^m(𝔄)` has `g - 1` in every
  `𝔓^m`, hence `g - 1 = 0` (`SplitObstruction.eq_zero_of_forall_ge_mem`). A decreasing sequence
  of compact closed sets whose intersection lies in an open neighbourhood has a member inside
  that neighbourhood (`exists_subset_nhds_of_isCompact'`).
- `exists_unitFiltration_subset_nhds`: every neighbourhood of the identity of `GL_n(F)` contains
  the image of some `U^m(𝔄)` under `Matrix.GeneralLinearGroup.toLin.symm`. The neighbourhood is
  transported from `GL_n(F)` to `A^×` by the homeomorphism `generalLinearToLinContinuous`, and
  `exists_unitFiltration_subset_nhds_aut` applies.
- `exists_unitFiltration_le_unitFiltration`: for lattice chains `𝓛`, `𝓜` in `F^n` and any `m`,
  some `U^k(𝓛)` lies in `U^m(𝓜)`. The group `U^m(𝓜)` is open (`isOpen_unitFiltration`), hence a
  neighbourhood of the identity, and `exists_unitFiltration_subset_nhds_aut` applies to `𝓛`.
- `finiteIndex_unitFiltration_subgroupOf_simpleJGroup`: for lattice chains `L`, `M` in `F^n`,
  `U^m(M) ∩ J^j(β, 𝔄)` has finite index in `J^j(β, 𝔄)`. The group `J^j(β, 𝔄)` contains some
  `U^t(𝔄)` (`exists_unitFiltration_le_simpleJGroup`), so it is open, hence closed, and lies in the
  compact group `U^0(𝔄)`, so it is compact. The subgroup `U^m(M) ∩ J^j(β, 𝔄)` is open in it, and
  an open subgroup of a compact group has finite index (`Subgroup.quotient_finite_of_isOpen`).
