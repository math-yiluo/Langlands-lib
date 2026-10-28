# Disjoint cells below a diagonal uniformizer element

This module supplies the lower bound for the integral of a matrix coefficient
used in the proof of
`Langlands.GLProductLeviTemperedExponentNecessityStatement`. All results are
internal helpers; none is a published statement. The idea is the usual one in
Casselman's exponent criterion: count the unipotent translates of a double coset
`g ^ M K`. This module does the counting explicitly for a diagonal uniformizer
element of one block. The Lean route is internal to this project.

## Off-diagonal unipotent matrices

For `S : Finset (Fin N)`, `Pairs S` is the subtype of index pairs `(a, b)` with
`a ∈ S` and `b ∉ S`. Its cardinality is `S.card * Sᶜ.card` (`card_pairs`).
`offMatrix S X` is the matrix with the entries of `X` at these positions and
zero elsewhere. Any two such matrices multiply to zero (`offMatrix_mul`), so
`unip S X = 1 + offMatrix S X` is invertible with inverse `1 - offMatrix S X`,
and `X ↦ unip S X` is a homomorphism from the additive group
(`unip_add`, `unip_zero`, `unip_neg`, `unip_inv_mul`).

If `d` is the diagonal matrix with `τ` on `S` and `1` elsewhere, then
`d⁻¹ * unip S X * d = unip S (τ⁻¹ • X)` (`unip_mul_diagonal`,
`inv_mul_unip_mul`).

## Integrality modulo the centre

`le_one_of_unip_eq`: if `unip S Y = k * s` with `k` in the maximal compact
subgroup `GL_N(O)` and `s` central, then every entry of `Y` is integral. Write
`s` as the scalar `c`. The diagonal entries of `k⁻¹ = s * unip S (-Y)` are `c`,
so `c` is integral, and `Y x = k_{ab} c`.

## Uniformizer digits

`residueLift` chooses an integral lift of a residue class. For
`δ : Fin m → T.ResidueField`, `digitVal T δ = ∑ s, ϖ ^ s * residueLift (δ s)`.
This element is integral (`digitVal_le_one`). If two digit expansions of length
`m` agree to level `m`, they are equal (`eq_of_level_digitVal_sub`). The proof is
by induction on `m` and peels off the constant digit with the residue map.
`level_of_uniformizer_pow_mul`, `level_one_uniformizer_mul` and
`level_uniformizer_pow_mul` move uniformizer powers across the level predicate
`CartanQuotient.CellCount.Level`.

## Small unipotent elements

`continuous_unip`: `unip S` is continuous. `exists_unip_mem`: for every open
subgroup `K` of the product Levi there is `t : ℕ` such that every `unip S` of
`ϖ ^ t` times an integral tuple, placed in block `j` by `Pi.mulSingle`, lies in
`K`. The proof uses the product neighbourhood filter (`nhds_pi`,
`Filter.mem_pi'`) and `T.exists_additiveLattice_subset` in each coordinate.

## Disjointness of the cells

Let the `j`-th component of `g` be the diagonal matrix with `ϖ` on `S` and `1`
elsewhere. `level_of_mk_eq`: if
`mulSingle j (unip S Y) * g ^ M * k` and `mulSingle j (unip S Y') * g ^ M * k'`
have the same image modulo the centre, and `k j`, `k' j` lie in `GL(O)`, then
`Y' - Y` has level `M` in every coordinate. The proof compares `j`-th
components (`Subgroup.center_pi`), conjugates the unipotent difference by
`g ^ M` and applies `le_one_of_unip_eq`.

## Lower bound for an integral over disjoint translates

`card_mul_le_lintegral`: let `μ` be a left-invariant measure on `G ⧸ Z` and
`K ⊆ G` open. Suppose the left translates by `h i` of the image of `K` are
pairwise disjoint and `a ≤ f` on each of them. Then
`card ι * (a * μ (image of K)) ≤ ∫⁻ f ∂μ`.

## Cell lower bound

`cells_lower_bound` combines these results. Let `KP` be an open subgroup inside
the integral product Levi. Let `f` take the value `F0 M` on every
`mk (u * g ^ M * k)` with `u, k ∈ KP`. Then there is `t` such that for every
`m`

`q ^ (m * |S| * |Sᶜ|) * (F0 (m + t) * μ (mk '' KP)) ≤ ∫⁻ f ∂μ`.

The translating elements are `mulSingle j (unip S (ϖ ^ t * digitVal δ))` with
`δ : Pairs S → Fin m → ResidueField`. The choice of `t` from `exists_unip_mem`
puts them in `KP`. Disjointness follows from `level_of_mk_eq` and digit
injectivity.
