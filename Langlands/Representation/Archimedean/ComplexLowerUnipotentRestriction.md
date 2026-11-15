# Principal-series functions are determined on the lower unipotent group

Lean module: `Langlands.Representation.Archimedean.ComplexLowerUnipotentRestriction`
(namespace `Langlands.Archimedean`; helpers in `Langlands.Archimedean.LowerUnipotentRestriction`).

## Statement

```lean
def ComplexPrincipalSeriesLowerUnipotentDeterminingStatement : Prop :=
  ∀ (n : ℕ) (χ : ℕ → ℂˣ → ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ),
    f ∈ principalSeries ℂ n χ → (∀ L ∈ lowerUnipotent n ℂ, f L = 0) → f = 0
```

Take any `n`, any characters `χ` and any function `f` of the Library's smooth principal series
`principalSeries ℂ n χ` of `GL_n(ℂ)`. These are the smooth functions with
`f(diag(a) u g) = principalSeriesCharacter ℂ n χ a · f(g)` for `u` upper unipotent. If `f`
vanishes on the Library's lower unipotent subgroup `lowerUnipotent n ℂ` (module
`Langlands.Group.GL.UpperBruhatCells`: zero above the diagonal, one on it), then `f = 0`. So a
principal-series function is determined by its restriction to the lower unipotent group.
`complexPrincipalSeriesLowerUnipotentDetermining` proves the statement.

Provenance: internal infrastructure for Task 7064. It supports the noncompact picture
(restriction to `N̄`) used for the growth bound `ComplexLinkedSmallGrowthStatement`.
Mathematically, it expresses the density of the big cell `B N̄` in `GL_n(ℂ)`. The proof is
self-contained.

## Proof

- `CornerNonzero m h` is defined recursively: `det h ≠ 0`, and the matrix obtained by deleting
  the first row and column satisfies `CornerNonzero` again. Equivalently, every lower-right
  corner minor of `h` is nonzero. `det_ne_zero_of_cornerNonzero` extracts `det h ≠ 0`.
- `exists_upper_mul_lower_of_cornerNonzero` (LU decomposition on the big cell): such an `h` is
  `b L` with `b` upper triangular and `L` lower unipotent (`IsLowerUnipotent`). The proof is
  induction on the size. Write `h` in blocks with first row `(h₀₀, row)`, first column
  `(h₀₀, col)` and corner block `h'`. The induction hypothesis gives `h' = b' L'`, and `b'` is
  invertible because `det L' = 1` (`det_eq_one_of_isLowerUnipotent`). Put `ℓ = b'⁻¹ col`,
  `r = row L'⁻¹` and `β = h₀₀ - r · ℓ`. Then `b = [[β, r], [0, b']]` and
  `L = [[1, 0], [ℓ, L']]` work. The four block entries of `b L` are checked with
  `Fin.sum_univ_succ`.
- `finite_setOf_not_cornerNonzero`: for every matrix `g`, only finitely many `t` fail
  `CornerNonzero (g + t·1)`. At each level, `det(g + t·1)` is the characteristic polynomial of
  `-g` evaluated at `t`. This polynomial is monic, so it has finitely many roots. Deleting the
  first row and column commutes with adding `t·1`.
- `eq_zero_of_cornerNonzero`: if `f` vanishes on `lowerUnipotent n ℂ` and `g` satisfies
  `CornerNonzero`, then `f g = 0`. Write `g = b L`, then `b = D u` with `D` the diagonal of `b`
  (Library `Iwasawa.diagonalUnits`) and `u = D⁻¹ b` upper unipotent. The equivariance in
  `mem_principalSeries_iff` gives `f g = principalSeriesCharacter(D) · f(L) = 0`.
- `eq_zero_of_eqOn_lowerUnipotent`: for any `g`, the matrices `g + t·1` with real `t → 0`,
  `t ≠ 0`, eventually satisfy `CornerNonzero`, so the extension `unitsExtension f` (Library,
  module `PrincipalSeriesStability`) vanishes at them. That extension is continuous at `g`
  (`contDiffOn_unitsExtension`), so `f g` is a limit of zeros and hence `0`.
