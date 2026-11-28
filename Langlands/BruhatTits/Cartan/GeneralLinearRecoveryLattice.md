# Conjugates of the integral general linear group over a valued field

Module `Langlands.BruhatTits.Cartan.GeneralLinearRecoveryLattice`, namespace
`Langlands.BruhatTits.Cartan.GeneralLinearRecovery`.

This module contains elementary matrix facts about `K = GL_N(𝒪)` inside
`GL_N(F)`. They are used by
[`GeneralLinearRecoveryProof`](GeneralLinearRecoveryProof.md) to identify a
vertex parahoric of `GL_N` with a conjugate of `K` by a diagonal matrix. Here `F`
is a field, `v : Valuation F Γ₀` is a valuation with values in a linearly ordered
commutative group with zero, and `𝒪 = v.integer`.

## Definitions

- `EntryBounded v M r`: every entry of the `N × N` matrix `M` has valuation at
  most `r`.
- `IsIntegral v g`, for `g : GL (Fin N) F`: `g` and `g⁻¹` have entries of
  valuation at most `1`. By `mem_range_map_iff`, these are exactly the matrices
  in the image of `Matrix.GeneralLinearGroup.map (algebraMap v.integer F)`, that
  is, the image of `GL_N(𝒪)` in `GL_N(F)`.
- `ColumnSupported M`: each column of `M - 1` has at most one nonzero entry.
  Diagonal matrices have this property, and so do the matrices `1 + e_a wᵀ`
  whose only off-identity entries lie in one row `a`.

## Results

**`isIntegral_inv_mul_mul_of_conj`.** If `k g k⁻¹ ∈ K` for every `g ∈ K`, then
`k⁻¹ g k ∈ K` for every `g ∈ K`. Hence `k K k⁻¹ ⊆ K` implies `k K k⁻¹ = K`.

The proof has three steps.

1. `conj_single_bounded`: the matrix `k E_{ij} k⁻¹` has integral entries for all
   `i, j`. For `i ≠ j` the matrix `1 + E_{ij}` lies in `K`, with inverse
   `1 - E_{ij}`. Its conjugate is `1 + k E_{ij} k⁻¹`. For `i = j` there are two
   cases. If `N ≥ 2`, write `E_{ii} = E_{im} E_{mi}` with `m ≠ i`. If `N = 1`,
   then `E_{ii} = 1`.
2. By `mul_single_mul_apply`, the `(p, q)` entry of `k E_{ij} k⁻¹` is
   `k_{pi} (k⁻¹)_{jq}`. In `exists_scalar_of_conj`, let `c` be an entry of `k` of
   maximal valuation. Then `c⁻¹ k` and `c k⁻¹` have integral entries. For
   `N = 0` the statement is empty.
3. Finally `k⁻¹ g k = (c k⁻¹) g (c⁻¹ k)`, and `EntryBounded.mul` bounds the
   product.

**`exists_diagonal_conj_bound`.** For `A ∈ GL_N(F)` there are units
`l_1, …, l_N` with the following property. Let `g ∈ GL_N(F)` be such that
`A⁻¹ g A` has integral entries and `g` is `ColumnSupported`. Then
`v(l_i⁻¹ g_{ij} l_j) ≤ 1` for all `i, j`.

Applied to `g` and to `g⁻¹`, this places `g` in `t K t⁻¹` for
`t = diag(l_1, …, l_N)`. The construction runs as follows.

- Let `B = A⁻¹`. For each column `j`, choose a row `p(j)` where `B_{p(j) j}` has
  maximal valuation. This entry `μ_j` is nonzero because `B` is invertible. Put
  `l_j = μ_j⁻¹`.
- `diagonal_conj_bound_aux` proves the bound. With `T = diag(l)`, the matrix
  `B T` has integral entries by the choice of `p(j)`. Hence so does
  `B (g - 1) T = (B g A)(B T) - B T`.
- Always `l_i⁻¹ g_{ij} l_j = δ_{ij} + μ_i (g - 1)_{ij} l_j`. If
  `(g - 1)_{ij} = 0`, this is `δ_{ij}`, which is integral. If
  `(g - 1)_{ij} ≠ 0`, the column condition makes `(g - 1)_{rj} = 0` for every
  `r ≠ i`. So the `(p(i), j)` entry of `B (g - 1) T` reduces to the single term
  `μ_i (g - 1)_{ij} l_j`, which is therefore integral, and the bound follows.

## Mathematical meaning and provenance

In lattice language, put `L = A 𝒪^N`, so that `A K A⁻¹ = GL(L)`. The vector
`l_j e_j` spans the intersection of `L` with the line `F e_j`. The bound says that
a column-supported element of `GL(L)` also maps the lattice
`⊕ 𝒪 l_j e_j` into itself. The first result says that a conjugate of `GL_N(𝒪)` contained in
`GL_N(𝒪)` equals it, that is, `k ∈ F^× · GL_N(𝒪)`.

Both are standard facts about lattices in `F^N`. They underlie the description
of the vertex stabilizers of `GL_N` as the groups `GL(L)` in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (Cambridge University Press, 2023),
Proposition 15.1.31 (printed p. 523, PDF p. 554; literature ID
`kaletha-prasad-2023-bruhat-tits-new-approach`). The proof given there uses a
volume argument for `gL ⊆ L`; the first result above replaces it by the
entrywise argument described. The module states and proves both facts directly
for matrices over an arbitrary valued field. It uses no building data and no
Cartan decomposition.
