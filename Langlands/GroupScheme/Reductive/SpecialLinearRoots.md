# Maximality of the diagonal torus of the special linear group, and its roots

Helper module for the proof of
`Langlands.GroupScheme.SpecialLinearSimplyConnectedPinningStatement`. Author: Worker 61
(Task 5703). It proves that the diagonal torus `diagonalTorus n k` of
`Reductive.SpecialLinearTorus` is a maximal torus of `SL_{n+1}` over a field `k`. It also
determines the roots of `SL_{n+1}` with respect to this torus. All declarations are in
namespace `Langlands.GroupScheme.SpecialLinear.FinSucc`. Let `𝔻` be the split torus
`splitTorus.commGroupScheme (Spec k) (ULift (Fin n))`. Write `w(p)` for
`weightCoord n p`, and `X_{pq}` for `lieMatrix X p q`.

## Maximality over a field

- `mem_weightSpace_zero_iff`: a Lie algebra element `X` lies in the zero weight space if and
  only if its matrix is diagonal (`X_{xy} = 0` for `x ≠ y`). This follows from
  `mem_weightSpace_diagonalTorus_iff_support` and `weightCoord_injective`.
- `zeroWeightCoord n k`: the `k`-linear map from the zero weight space to `Fin n → k` that
  takes the first `n` diagonal entries `X_{a.castSucc, a.castSucc}`. `zeroWeightCoord_apply`
  unfolds it.
- `lieMatrix_eq_zero_of_zeroWeightCoord`: an element of the zero weight space whose first
  `n` diagonal entries vanish is `0`. Its matrix is diagonal, and the last diagonal entry is
  `0` because the trace vanishes (`trace_lieMatrix`).
- `diagonalEntries d = Fin.snoc d (-∑ a, d a)`, with `trace_diagonal_diagonalEntries`: the
  diagonal matrix of these entries has trace zero.
- `zeroWeightCoord_bijective`. Injectivity is `lieMatrix_eq_zero_of_zeroWeightCoord`.
  Surjectivity: the trace-zero diagonal matrix of `diagonalEntries d` is the matrix of a Lie
  algebra element (`exists_lieMatrix_eq`), and that element has weight zero.
- `finrank_weightSpace_zero`: the zero weight space has dimension `n` over `k`.
- `isMaximalTorus_diagonalTorus n k`: **the diagonal torus is a maximal torus** in the
  Library's sense (`IsMaximalTorus`). This is the Library criterion
  `isMaximalTorus_of_finrank_zeroWeight`. A split subtorus whose zero weight space has the
  dimension of the torus's own Lie algebra is maximal. Here both dimensions are `n`
  (`finrank_weightSpace_zero` and the Library's `splitTorus.finrank_lieKernel`).

## Roots

The roots are the Library's `roots (diagonalTorus n k)`: the nonzero characters `χ` of `𝔻`
with nonzero weight space. Coordinates of characters are the Library's
`GeneralLinear.characterCoordEquiv (Fin n) k`.

- `exists_coord_of_mem_roots`: every root `χ` has coordinates `w(p) - w(q)` for some
  `p ≠ q`. A nonzero vector of weight `χ` has a nonzero entry `X_{pq}`.
  `mem_weightSpace_diagonalTorus_iff_support` gives `χ = w(p) - w(q)`, and `p ≠ q` because
  `χ ≠ 0`.
- `rootChar n k p q : characterLattice 𝔻` is the character with coordinates
  `w(p) - w(q)`. `characterCoordEquiv_rootChar` records this.
- `rootChar_mem_roots`: for `p ≠ q`, `rootChar n k p q` is a root. It is nonzero by
  `weightCoord_injective`. The trace-zero matrix unit at `(p, q)` comes from a Lie algebra
  element (`exists_lieMatrix_eq`), which is a nonzero vector of this weight.
- `mem_roots_iff`: **the roots of `SL_{n+1}`.** A character is a root if and only if its
  coordinates are `w(p) - w(q)` for some distinct `p, q`.

## Provenance

The diagonal torus of `SL_{n+1}` is maximal, and its roots are `ε_p - ε_q` for `p ≠ q`. Both
facts are standard textbook material on `SL_{n+1}`. The maximality proof here uses the
Library's Lie-algebra dimension criterion instead of computing the centralizer directly. The
module was written for this project after the Library's `SymplecticMatrix.Roots`.
