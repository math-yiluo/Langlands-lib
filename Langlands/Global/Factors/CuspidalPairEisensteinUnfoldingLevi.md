# The Weyl element and the Levi on the open cell

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingLevi` (namespace
`Langlands.Global.CuspidalPairEisenstein.Unfolding`) proves the matrix identities that turn the
open-cell integrand into the integrand of the Levi Whittaker coefficient `leviWhittaker` of
[CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md).

The main identity, `w diag(A, B) w⁻¹ = diag(B, A)` for the block Weyl element `w` of the
two-block parabolic of `GL_N`, is a direct block-matrix calculation proved here
(`openCellWeyl_mul_leviHom`). It moves the Levi variable of the open cell across `w`. The
open-class stabilizer comes from Shahidi, *Functional equation satisfied by certain
L-functions*, Compositio Math. 37 (1978), proof of Lemma 2.1, paragraph after (2.10.3), p. 182,
where the class of `w₀` has the stabilizer `V = w₀Pw₀⁻¹ ∩ U`. Its two-block `GL_N` counterpart
is `N_(M') = N_(t+1) × N_(r+1)`
([CuspidalPairEisensteinUnfoldingOpenGroups.md](CuspidalPairEisensteinUnfoldingOpenGroups.md)),
which the identity carries to the upper unitriangular group of the Levi `M` of `P`. Shahidi,
*On certain L-functions*, Amer. J. Math. 103 (1981), proof of Theorem 5.1, p. 351, later applies
Lemma 2.1 of the 1978 paper to factor the Fourier coefficient into local Whittaker functions.

## Block coordinates of the Levi

- `leviBlocks r t : Fin (r + 1) ⊕ Fin (t + 1) ≃ Fin (r + t + 2)` lists the block of size `r + 1`
  first, as in `blockShape r t` (`leviBlocks_inl_val`, `leviBlocks_inr_val`).
- `openCellPermutation_swapBlocks`, `openCellPermutation_symm_leviBlocks`: the block Weyl
  permutation carries the coordinates `swapBlocks` (block `t + 1` first) to `leviBlocks` with
  the two summands exchanged.
- `blockShape_leviEmbedding_apply` (over any commutative ring) and `leviPair_apply`: in the
  coordinates `leviBlocks`, `leviPair x y` is `fromBlocks x 0 0 y`.

## Identities

- `openCellWeyl_mul_leviHom`: for `m = (A, B) ∈ N_(t+1)(𝔸) × N_(r+1)(𝔸)`,
  `w · diag(A, B) = leviPair B A · w`. Here `diag(A, B)` is `leviHom m`, block diagonal in the
  coordinates `swapBlocks`, and `w = openCellWeyl F r t`. The proof compares
  `w diag(A, B) w⁻¹` with `leviPair B A` entry by entry through the permutation.
- `toMat_leviHom_apply` and `sum_superdiag_leviHom`: the superdiagonal of `diag(A, B)` is that
  of `A`, then a zero at the junction, then that of `B`. Hence `genericChar_leviHom`:
  `ψ_N(diag(A, B)) = ψ_(t+1)(A) ψ_(r+1)(B)`, with the Library's `genericCharacter` for the
  coefficients `1`.
- `genericChar_radicalHom`: `ψ_N(u'(Y)) = ψ(Y_(t,0))`, by `openCellUnipotent_superdiagonal_sum`.
- `leviPair_mul`: `leviPair` is multiplicative. `leviPair_rational`: the image of a pair of
  rational matrices is the image of an element of `P(F)`.
