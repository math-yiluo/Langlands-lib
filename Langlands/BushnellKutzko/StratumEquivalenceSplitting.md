# Relative splitting bases for a normalizing field

Helper module for the proof of `Langlands.BushnellKutzko.StratumEquivalenceStatement`
(Bushnell–Kutzko 1993, (2.1.4)(iii), printed p. 50). It restates as public lemmas the
arguments of the private lemmas of the published module
`Langlands.BushnellKutzko.RelativeFiltrationInversion`, which are not accessible outside
that file. The setting is a field `E` acting on the `F`-space `V` (compatibly with `F`) whose
units normalize an `𝔬_F`-lattice chain `𝓛 = (L_i)`.

- `exists_scalar_lattice_shift`: a nonzero `c ∈ E` shifts the chain: `c v ∈ L_{i+d}` iff
  `v ∈ L_i`, with `d` the stabilizer valuation of `c`.
- `exists_lattice_maximal_coset_rep` (`F` a nonarchimedean local field): for an
  `E`-subspace `U` and `x ∉ U`, some representative `w` of `x + U` lies in every lattice that
  meets `x + U` (a base-field section of `V → V/U` bounds the depths of representatives; the
  greatest depth is attained).
- `coset_rep_smul_mem_of_add_mem`: for such a representative `w`, `u ∈ U` and any `c ∈ E`,
  `u + c w ∈ L_i` implies `c w ∈ L_i`. This is trivial for `c = 0`. For `c ≠ 0` with shift
  `d`, the vector `y = c⁻¹ u + w` satisfies `c y = u + c w ∈ L_i`, so `y ∈ L_{i-d}`; since
  `y - w ∈ U`, maximality gives `w ∈ L_{i-d}`, hence `c w ∈ L_i`.
- `RelativeSplits` (an internal notion): a finite family `w` splits the chain if every summand
  `c_j w_j` of a combination lying in `L_i` lies in `L_i`. `relativeSplits_finCons`: adjoining a
  maximal coset representative preserves splitting.
- `exists_relative_splitting_basis` (`F` a nonarchimedean local field, `dim_F V < ∞`): there
  is an `E`-basis of `V` splitting the chain (a splitting linearly independent family of
  greatest length spans `V`).
- `exists_scaled_basis_at_depth`: for a splitting basis, for every `i` some `c w_j` lies in
  `L_i` but not in `L_{i+1}`.
- `coord_smul_mem`: for a splitting basis, `v ∈ L_i` implies `coord_k(v) w_k ∈ L_i`.

Source. The corresponding object in BK93 is a basis of a lattice chain in the sense of
(1.1.7), printed p. 23. The paragraph following (1.1.8), on the same page, states that every
`𝔬_F`-lattice chain has such a basis. By (1.2.1), printed p. 24, the chain of a normalizing
field `E` is an `𝔬_E`-lattice chain in the `E`-space `V`, so that statement, applied over
`𝔬_E`, gives an `𝔬_E`-basis of the chain. Proposition (1.2.8), printed p. 26, uses such a
basis for the decomposition (1.2.9). A splitting basis here (`RelativeSplits`) is the
corresponding relative notion without normalization: each `L_i` is the sum of its
intersections with the lines `E w_k`, but the `w_k` need not span a lattice of the chain.
Here its existence is proved directly as above, not taken from BK93.
