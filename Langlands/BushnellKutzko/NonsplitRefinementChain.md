# Refining a lattice chain by the images of a residually nilpotent element

Module `Langlands.BushnellKutzko.NonsplitRefinementChain`, namespace
`Langlands.BushnellKutzko.NonsplitRefinement`. It imports `Langlands.BushnellKutzko.MoyReduction`
and `Langlands.BushnellKutzko.CriticalDerivedCyclicRows`. It supplies the finer lattice chain in
the proof of BK93 (2.3.4) in `NonsplitRefinementProof`.

## Setting

`F` is a nonarchimedean local field with uniformizer `ϖ`, `V` an `F`-vector space and
`𝓛 = (L_i)` an `𝔬_F`-lattice chain in `V` with period `e`. Write `𝔄(𝓛) = 𝔓^0(𝓛)` and
`𝔓(𝓛) = 𝔓^1(𝓛)`, with `𝔓^j(𝓛) = 𝓛.endFiltration j`. A unit `g` *shifts* a chain by `d`
(`CriticalDerived.Shifts`) if `g ∈ 𝔓^d` and `g⁻¹ ∈ 𝔓^{-d}`, that is, `g L_i = L_{i+d}` for all
`i`.

## The image lattices

For `z ∈ 𝔄(𝓛)`, `imageLattice 𝓛 z i t` is the `𝔬_F`-lattice `z^t L_i + L_{i+1}`. Suppose
`z^m ∈ 𝔓(𝓛)`. Then:

- `L_{i+1} ⊆ z^t L_i + L_{i+1} ⊆ L_i`, the lattice at `t = 0` is `L_i`, the lattices at `i`
  decrease in `t`, and they equal `L_{i+1}` for `t ≥ m` (`imageLattice_le`,
  `imageLattice_zero`, `imageLattice_antitone`, `imageLattice_of_le`);
- `z^{t+1} L_i + L_{i+1} = z(z^t L_i + L_{i+1}) + L_{i+1}` (`imageLattice_succ`). Consequently,
  if two consecutive lattices at `i` agree, both are `L_{i+1}`
  (`imageLattice_eq_of_succ_eq`);
- a unit commuting with `z` and shifting `𝓛` by `d` maps the lattices at `i` onto those at
  `i + d` (`map_imageLattice_of_shifts`);
- any two image lattices are comparable (`imageLattice_le_total`), and every image lattice is an
  image lattice at an index `i` at which it strictly contains `L_{i+1}`
  (`exists_imageLattice_eq_sandwich`).

## The chain

`exists_latticeChain_range_eq` is the statement of the same name in `MoyReduction`, for an
arbitrary vector space `V` in place of `F^ι`, with the same proof: a nonempty totally ordered set
of lattices, stable under all powers of `ϖ`, on which `ϖ` acts strictly decreasingly and whose
intervals are finite, is the set of lattices of a lattice chain. The supporting lemmas on the
pointwise action of units of `F` on submodules are proved in the same way.

`exists_imageChain` applies it to the set of all image lattices, which is nonempty since it
contains the image lattice at `(0, 0)`. Scaling by `ϖ^k` is the image
under a scalar unit that shifts `𝓛` by `k e` (`units_smul_eq_map`, `uniformizerUnit_shifts`), so
it maps the lattices at `i` onto those at `i + k e`. Strictness of the action of `ϖ` comes from
the representation at an index where the lattice strictly contains `L_{i+1}`. An interval
between the lattices at `(i, t)` and `(i', t')` contains only lattices at indices between
`i - 1` and `i' + 1` with `t ≤ m`, so it is finite.

## Main result

`exists_refinement hϖ hz hzm hb hbz`. Let `z ∈ 𝔄(𝓛)` with `z^m ∈ 𝔓(𝓛)`, and let `b` be a unit
of `End_F(V)` that commutes with `z` and shifts `𝓛` by `ℓ`. Then there are a lattice chain `𝓜`
and an integer `ℓ'` such that

1. `b` shifts `𝓜` by `ℓ'`;
2. every `L_i` is a lattice of `𝓜`;
3. `𝔓^{ℓ+1}(𝓛) ⊆ 𝔓^{ℓ'+1}(𝓜)`;
4. `z ∈ 𝔓(𝓜)`;
5. every unit of `𝔄(𝓛)` (a unit shifting `𝓛` by `0`) that commutes with `z` is a unit of `𝔄(𝓜)`.

The chain `𝓜` is the one of `exists_imageChain`. By `map_imageLattice_of_shifts`, `b` maps
lattices of `𝓜` to lattices of `𝓜`, so `LatticeChain.exists_shift` gives `ℓ'`, and
`shifts_of_map_eq` turns this into a shift. For (3) and (4), write a lattice of `𝓜` as
`M = z^t L_i + L_{i+1}` with `L_{i+1} ⊊ M`. If `x ∈ 𝔓^{ℓ+1}(𝓛)`, then `x M ⊆ L_{i+ℓ+1}`, and
`L_{i+ℓ+1} = b L_{i+1} ⊊ b M`, which is the lattice `ℓ'` steps after `M`; hence
`L_{i+ℓ+1}` lies in the next lattice. Similarly `z M ⊆ z^{t+1} L_i + L_{i+1}`, which is strictly
smaller than `M` by `imageLattice_eq_of_succ_eq`. Statement (5) is
`map_imageLattice_of_shifts` with `d = 0`.

## Mathematical role

In BK93 §2.5, printed pp. 76–83 (`bushnell-kutzko-1993-admissible-dual-gln`), the finer chain
of (2.3.4) is the principal chain with blocks of size `deg φ` attached to a Jordan canonical
form (2.5.7)–(2.5.11). Here the finer chain is the filtration of each quotient `L_i/L_{i+1}` by
the images of the powers of `z = P(y)`, where `P` lifts the irreducible factor of the
characteristic polynomial; on its successive quotients `P(y)` acts by zero.
