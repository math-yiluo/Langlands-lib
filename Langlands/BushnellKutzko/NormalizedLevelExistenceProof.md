# L0: existence of the normalized level (proof)

Module `Langlands.BushnellKutzko.NormalizedLevelExistenceProof`, namespace
`Langlands.BushnellKutzko`. It proves the published proposition
`NormalizedLevelExistenceStatement.{uK, uV}` of
`Langlands.BushnellKutzko.NormalizedLevelExistenceStatement`, with both universes
arbitrary. The closing theorem is

- `normalizedLevelExistence : NormalizedLevelExistenceStatement.{uK, uV}`.

The proof adds no hypotheses. Its only axioms are `propext`, `Classical.choice` and
`Quot.sound`. It uses the Library's lattice chains, unit filtrations and periods
(`Langlands.BushnellKutzko.LatticeChain`, `UnitFiltration`), the definitions
`unitSubgroup` and `normalizedLevelValues` of `Langlands.BushnellKutzko.NormalizedLevel`, and
two Library facts about principal congruence subgroups
(`Langlands.Representation.Conductor.PrincipalCongruenceBasisProof`):
`Conductor.mem_principalCongruenceSubgroup_iff` and
`Conductor.exists_pos_principalLevelOpenSubgroup_subset`.

Mathematical source: the remark under L0 in the statement's Markdown. The
set of values is nonempty by smoothness, and it lies in `(1/n!) ℕ` because
`1 ≤ e(𝓛) ≤ n`. Bushnell (1987), (3.3), printed p. 196, takes this minimum without
comment. The bound `e(𝓛) ≤ n` comes from the strict chain `L_0 ⊋ L_1 ⊋ ⋯ ⊋ L_e = 𝔭 L_0`,
which gives a strict chain of subspaces of `L_0 / 𝔭 L_0 ≅ k_F^n`; this module proves it.
The Lean proof follows this route; the parts are described below.

## 1. The period is at most the dimension

`LatticeChain.period_le_card` holds for any nonarchimedean local field `F` (instances
`Field`, `ValuativeRel`, `TopologicalSpace`, `IsNonarchimedeanLocalField`), any finite type
`ι` and any `𝓛 : LatticeChain 𝒪[F] F (ι → F)`. It states `𝓛.period ≤ Fintype.card ι`.

Proof. Write `e = 𝓛.period` and `L0 = 𝓛.lattice 0`. Let `N j ≤ L0` be the lattice
`L_j` pulled back to a submodule of `L0`, for `j : ℕ`. The chain property
`lattice_succ_lt` gives `N (j+1) < N j`. To see this, map both sides back into `F^ι` with
`Submodule.map_comap_subtype`, and use that `L_j ≤ L_0` for `j ≥ 0`. Periodicity
`lattice_add_period 0` and `jacobson_integer_eq_maximalIdeal` give
`N e = 𝔭_F • ⊤`, again by mapping into `F^ι` (`Submodule.map_smul''`).

Let `P j` be the image of `N j` in `L0 / N e`. For `j < e`, `P (j+1) < P j`; pull back
along the quotient map (`Submodule.comap_map_mkQ`) to check this. Induction with
`Order.coheight_add_one_le` gives `j ≤ coheight (P j)` for `j ≤ e`. Since `P e = ⊥`,
`Module.length_eq_coheight` gives `e ≤ length_{𝒪[F]} (L0 / N e)`.

The length is `#ι`. The quotient is `L0 / 𝔭_F L0`, a vector space over the residue
field `𝒪[F] / 𝔭_F`. Its length over `𝒪[F]` equals its length over the residue field
(`Module.length_eq_of_surjective`), which is its dimension (`Module.length_eq_finrank`).
`IsLocalRing.spanFinrank_eq_finrank_quotient` (Nakayama) turns this dimension into the
minimal number of generators of `L0`. `L0` is free over the discrete valuation ring
`𝒪[F]`, so this number is `finrank_{𝒪[F]} L0` (`Module.finrank_eq_spanFinrank_of_free`).
That rank is `#ι` by `Submodule.IsLattice.finrank_of_pi`.

## 2. The standard lattice chain

The proof uses the period-one chain from [Splitting basis](SplittingBasis.md).

- `LatticeChain.standardLattice F ι` is the lattice `𝔬_F^ι`, the range of the coordinatewise inclusion
  `(ι → 𝒪[F]) → (ι → F)`. `LatticeChain.mem_standardLattice` says `v ∈ 𝔬_F^ι` exactly when every coordinate
  is integral. The instance `LatticeChain.isLattice_standardLattice` proves that it is an `𝒪[F]`-lattice
  (`Submodule.IsLattice`) for finite `ι`: it is finitely generated, and it contains the
  standard basis.
- `LatticeChain.mem_smul_standardLattice`: for `u : Fˣ`, `v ∈ u • 𝔬_F^ι` exactly when `u⁻¹ v k ∈ 𝒪[F]` for
  every `k`. Here `Fˣ` acts on submodules through the pointwise action of `F`, so the proof
  rewrites with `Units.smul_def` first.
- For an irreducible `ϖ : 𝒪[F]` (a uniformizer), `LatticeChain.uniformizerAsUnit hϖ : Fˣ` is `ϖ` as a
  unit of `F`. `LatticeChain.inv_coe_uniformizer_not_mem` shows `ϖ⁻¹ ∉ 𝒪[F]`: otherwise `ϖ` would be a unit
  of `𝒪[F]`.
- `LatticeChain.standard hϖ ι : LatticeChain 𝒪[F] F (ι → F)`, for finite nonempty `ι`, is the chain
  `L_i = ϖ^i 𝔬_F^ι` (`i ∈ ℤ`). The inclusion `L_{i+1} ≤ L_i` holds because `ϖ` is integral.
  The inclusion is strict: `ϖ^i e_{k0}` lies in `L_i` but not in `L_{i+1}`, since
  `ϖ⁻¹ ∉ 𝒪[F]`. The period witness is `1`. Here `𝔭_F = (ϖ)` (`Irreducible.maximalIdeal_eq`),
  `Submodule.ideal_span_singleton_smul` turns `𝔭_F • L_i` into `ϖ • L_i`, and `ϖ • L_i`
  is checked to equal `ϖ^{i+1} 𝔬_F^ι` elementwise.

## 3. Unit groups of the standard chain lie in principal congruence subgroups

- `exists_mem_pow_of_mem_unitFiltration`: if `toLin g` lies in `U^N` of the standard chain,
  then every entry `g i j - δ i j` is the image of an element of `𝔭_F^N`. Apply
  `(g - 1) L_0 ⊆ L_N` to the basis vector `e_j`. Its `i`-th coordinate is `g i j - δ i j`.
  It lies in `ϖ^N 𝒪[F]`, so the witness is `ϖ^N · (ϖ^{-N} (g i j - δ i j))`.
- `unitSubgroup_stdChain_le n N g hg`: if `toLin g ∈ U^N` of the standard chain in
  `F^{n+1}`, then `g ∈ Conductor.principalLevelSubgroup F n N`. The Library criterion
  `Conductor.mem_principalCongruenceSubgroup_iff` asks for the entry condition for `g` and
  for `g⁻¹`. The second follows from the first, because `U^N` is a subgroup and `toLin`
  respects inverses (`map_inv`).

## 4. Least elements of sets of multiples of `1/D`

`exists_isLeast_of_mul_mem_nat`: let `S ⊆ ℚ` be nonempty and `D > 0`, and suppose every
`x ∈ S` has `x · D ∈ ℕ`. Then `S` has a least element. Proof: `Nat.find` gives the least
natural number of the form `x · D` with `x ∈ S`, and the corresponding `x` is least,
because `D > 0`.

## 5. Proof of L0

The section uses the same canonical instances on `K.Carrier` and
`GeneralLinear n K.Carrier` as the statement module (from `K.canonicalTopologicalData` and
`K.canonicalGeneralLinearTopology`), as local instances.

- `normalizedLevelValues_nonempty K n a`: for a class `a` of `GL_{n+1}(K)`, the set
  `normalizedLevelValues K (n+1) a` is nonempty. Choose a representative `A`. It is
  irreducible, hence a simple module over the group algebra, hence nontrivial, so it has a
  vector `v ≠ 0`. Smoothness (`A.obj.isSmooth v`) gives an open subgroup `K0` fixing `v`.
  `Conductor.exists_pos_principalLevelOpenSubgroup_subset` gives `N ≥ 1` with
  `principalLevelSubgroup K n N ⊆ K0`. A uniformizer `ϖ` exists
  (`IsDiscreteValuationRing.exists_irreducible`). The value
  `(N - 1) / e(LatticeChain.standard)` belongs to the set: the image of `U^{(N-1)+1} = U^N` of the
  standard chain lies in `K0` by part 3, so it fixes `v`, and its fixed space is nonzero.
- `exists_mul_factorial_eq_of_mem_normalizedLevelValues K n a`: every element
  `m / e(𝓛)` of `normalizedLevelValues K n a`, multiplied by `n!`, is a natural number.
  By part 1, `e(𝓛) ≤ n`, and `e(𝓛) ≥ 1`, so `e(𝓛)` divides `n!` (`Nat.dvd_factorial`).
- `normalizedLevelExistence`: given `n ≥ 1`, write `n = n' + 1`. Apply part 4 with
  `D = n!` to the two facts above.
