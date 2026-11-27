# Unipotent orbits on a Grassmannian by row echelon forms

Module `Langlands.Global.Factors.CuspidalPairEisensteinRowEchelon` (namespace
`Langlands.Global.CuspidalPairEisenstein.RowEchelon`) is linear algebra over a field `K`. It
describes the orbits of the upper unitriangular group `N` on the cosets `P \ GL_n(K)`, where `P`
is the subgroup of all invertible matrices whose lower left block (rows `≥ a`, columns `< a`)
vanishes. The results on cosets of `P` assume exactly this description of `P` (hypothesis `hP`
below). This is the linear algebra of the
two-block `GL_n` analogue of the double coset decomposition used to unfold an Eisenstein series
against a generic character in Shahidi, *Functional equation satisfied by certain
L-functions*, Compositio Math. 37 (1978), proof of Lemma 2.1, (2.10.2)–(2.10.3), pp. 181–182.
Shahidi works with a split group `G` of type `G₂`, a maximal parabolic subgroup `P = MN`
containing a fixed Borel subgroup, and the unipotent radical `U` of that Borel subgroup (§1,
p. 173; §2, p. 176). For `GL_n` the counterpart of `U` is the upper unitriangular group, here
`N`. In (2.10.2) Shahidi groups the cosets `G_F/P_F` into the double cosets `U_F \ G_F / P_F`
with the stabilizers `γ P_F γ⁻¹ ∩ U_F`. In (2.10.3), p. 182, the Bruhat decomposition indexes
the double cosets by the classes `w ∈ W/W_M`. The source works with the right quotient
`G_F/P_F`. This module takes the left quotient `P \ GL_n(K)`, which corresponds to it under
inversion `g ↦ g⁻¹`, and indexes the double cosets by pivot sets instead of Weyl classes.

## Definitions

- `lowerRowSpace a g`: the span in `Kⁿ` of the rows of `g` with index at least `a`.
- `coordSpace J`: the coordinate subspace of the vectors supported on the finite set `J`.
- `LowerLeftZero a g`: the entries `g i j` with `a ≤ i` and `j < a` vanish.
- `IsLead v j`: `j` is the first nonzero coordinate of `v`. `pivots W` is the set of leading
  positions of the nonzero vectors of a subspace `W`.
- `stabilizer J` (over any commutative ring `R`): the pattern subgroup `Λ_J` of upper
  unitriangular invertible matrices whose entries `g i j` with `i ∈ J`, `j ∉ J` vanish. Over a
  field it is the stabilizer of `coordSpace J` in `N`.
- `PivotIndex n a`: the subsets of `Fin n` of size `n - a`. `StabilizerCosets J`: the right
  cosets `(Λ_J ∩ N) \ N`.
- `orbitMap a P rep`: the map `(J, Λ_J δ) ↦ P · rep J · δ`, with a chosen representative `δ` of
  each coset.

## Results

- `lowerRowSpace_mul_right`, `lowerRowSpace_mul_left_le`, `lowerRowSpace_one`,
  `finrank_lowerRowSpace`: right multiplication by `h` maps the span by `vecMulLinear h`. Left
  multiplication by a matrix with vanishing lower left block does not enlarge it. For the identity
  it is the coordinate space of `{i | a ≤ i}`, of dimension `n - a`.
- `card_pivots`: `(pivots W).card = finrank K W`. Vectors with distinct leading positions are
  linearly independent. Conversely, the restriction of `W` to the coordinates in its pivots is
  injective.
- `pivots_map_unipotent`: right multiplication by an upper unitriangular matrix preserves the
  pivots. `pivots_coordSpace`: the pivots of `coordSpace J` are `J`.
- `exists_unipotent_map_coordSpace` (**row echelon form**): every subspace `W` is the image of
  `coordSpace (pivots W)` under some upper unitriangular `u`. Since restriction to the pivot
  coordinates is a bijection, `W` has for each pivot `j` a vector `w_j` with coordinate `1` at
  `j` and `0` at the other pivots. Its leading position is `j`. The matrix with rows `w_j` at
  the pivots and standard basis rows elsewhere is upper unitriangular. It maps
  `coordSpace (pivots W)` into `W`, and the dimensions agree.
- `map_coordSpace_eq_iff`: two such images agree exactly when `u' u⁻¹ ∈ Λ_J`.
- `rightRel_iff`: if `P` consists exactly of the invertible matrices with vanishing lower left
  block (hypothesis `hP`), then `g` and `g'` lie in the same right coset of `P` exactly when
  `lowerRowSpace a g = lowerRowSpace a g'`.
- `orbitMap_bijective` (**orbit decomposition**): assume that `P` consists exactly of the
  invertible matrices with vanishing lower left block (`hP`), and that for every `J` of size
  `n - a` the rows `≥ a` of `rep J` span `coordSpace J` (`hrep`). Then `orbitMap` is a bijection
  from `Σ J : PivotIndex n a, StabilizerCosets J` onto `P \ GL_n(K)`. Both directions use
  `rightRel_iff`, hence `hP`, to identify a coset of `P` with the row span of its rows `≥ a`.
  Surjectivity takes the pivots `J` of the row span of `g` and the row echelon form. Injectivity
  uses the invariance of pivots and `map_coordSpace_eq_iff`. The hypothesis `hP` cannot be
  weakened to `P` being some subgroup of such matrices: for `K = ℚ`, `n = 2`, `a = 1` and
  `P = {1}`, the swap matrix for `J = {0}` and the identity for `J = {1}` satisfy `hrep`, but
  every element `rep J · δ` then has determinant `±1`, so the coset of the scalar matrix `2` is
  not in the image.
