# A basis adapted to a lattice chain and to its layer bases

Let `L` be an `𝒪[F]`-lattice chain of period `e` in an `F`-vector space `V`,
and `b i` a residue-field basis of the layer `L_i / L_(i+1)` for `0 ≤ i < e`,
indexed by `Fin f`. The adapted coordinates refine the lattice splitting in
BK93 (5.5.2), printed p. 181 (PDF p. 193), by lifting specified bases for the
level-zero data of (5.5.10)(b). [Source details](LevelZeroNonmaximalTypeJacquetProof.md#source)

- `liftVec L b (a, i)` is a chosen lift to `L_i` of `b i a`. The lemmas
  `liftVec_mem` and `intervalMk_liftVec` record its membership and image.
- `linearIndependent_liftVec` and `span_liftVec` show that the lifts form an
  `F`-basis, `adaptedBasis L b hϖ he`.
- `mem_lattice_iff_repr` characterizes `x ∈ L_j` for `0 ≤ j ≤ e` by integral
  coordinates in the adapted basis, with coefficients in the maximal ideal
  on blocks `i < j`.
- `mem_endFiltration_of_lt_period` tests membership in the endomorphism
  filtration on the lattices `L_j` with `0 ≤ j < e` by periodicity.
- `toLin_mem_endFiltration_iff` tests membership in `End^s(L)` for `s ∈ {0, 1}`.
  All matrix entries are integral, and the entries `M p q` with
  `p.2 < q.2 + s` lie in the maximal ideal. These are `InOrd` and `InRad` in
  the two cases. [Standard order](LevelZeroStandard.md)

Descending induction through the layers and Nakayama's lemma at
`L_e = 𝔭 L_0` show that the lifted vectors with the indicated coefficient
conditions span each `L_j` over `𝒪[F]`. Since `L_0` spans `V` over `F`, so do
the lifts. For linear independence, divide a vanishing combination by a
nonzero coefficient of largest valuation. In the first block containing a
unit coefficient, the combination then reduces to a nontrivial relation in
the layer basis. This is impossible.
