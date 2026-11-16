# Real principal-series functions are determined on the lower unipotent group

Module `Langlands.Representation.Archimedean.RealLowerUnipotentRestriction`, namespace
`Langlands.Archimedean.RealLowerUnipotent`.

## Results on the principal series

Let `χ : ℕ → ℝˣ → ℂ` and `f ∈ principalSeries ℝ n χ` (the Library smooth principal series of
`GL_n(ℝ)`: smooth functions with `f(diag(a) u g) = principalSeriesCharacter ℝ n χ a · f(g)` for
upper unipotent `u`).

* `eq_zero_of_cornerNonzero`: if `f` vanishes on the Library's `lowerUnipotent n ℝ`, then `f`
  vanishes at every `g` whose lower-right corner minors are all nonzero
  (`LowerUnipotentRestriction.CornerNonzero`).
* `eq_zero_of_eqOn_lowerUnipotent`: if `f` vanishes on `lowerUnipotent n ℝ`, then `f = 0`.

These are the real versions of the Library theorems `eq_zero_of_cornerNonzero` and
`eq_zero_of_eqOn_lowerUnipotent` (module `ComplexLowerUnipotentRestriction`, stated there for
`GL_n(ℂ)`).

## Coordinates on the lower unipotent group

* `LowIdx n`: the positions `(i, j)` of `Fin n × Fin n` with `j < i`.
* `nbarMat v`, for `v : LowIdx n → ℝ`: the matrix with entry `v (i, j)` at positions `j < i`, `1`
  on the diagonal and `0` above it. `isLowerUnipotent_nbarMat`, `det_nbarMat` (`= 1`),
  `isUnit_nbarMat`.
* `nbar v`: the corresponding element of `GL_n(ℝ)`. `nbar_val`: its matrix is `nbarMat v`.
  `nbar_inv_val`: its inverse is the adjugate of `nbarMat v`.
* `nbar_mem_lowerUnipotent`, and `exists_nbar_eq`: every element of `lowerUnipotent n ℝ` is
  `nbar v`, where `v` lists its entries below the diagonal.
* `eq_zero_of_nbar`: a function of `principalSeries ℝ n χ` that vanishes at every `nbar v` is `0`.

## Provenance

Internal infrastructure for the proof of `RealLeftPolynomialGrowthStatement` (Task 7070). It is
the density of the big cell `B N̄` in `GL_n(ℝ)`, a standard fact. The proof copies that of the
complex case in the Library and makes no literature assertion.

## Proofs

* `eq_zero_of_cornerNonzero`: by the Library's field-general
  `LowerUnipotentRestriction.exists_upper_mul_lower_of_cornerNonzero`, `g = b L` with `b` upper
  triangular and `L` lower unipotent. Since `det g ≠ 0`, the diagonal entries of `b` are nonzero.
  So `b = D u` with `D = diag(b_ii)` and `u = D⁻¹ b` upper unipotent. The equivariance of `f` gives
  `f(g) = principalSeriesCharacter ℝ n χ (b_ii) · f(L) = 0`.
* `eq_zero_of_eqOn_lowerUnipotent`: `f̃ = unitsExtension f` is continuous at `g`. By the
  field-general `LowerUnipotentRestriction.finite_setOf_not_cornerNonzero`, `g + t·1` has nonzero
  corner minors for all but finitely many real `t`. So `f̃(g + t·1) = 0` for `t ≠ 0` near `0`, by
  the first result. Letting `t → 0` gives `f(g) = f̃(g) = 0`.
* `nbar_inv_val`: `(nbarMat v)⁻¹ = (det)⁻¹ · adjugate`, and the determinant is `1`.
* `exists_nbar_eq`: compare entries, using the entry description of `lowerUnipotent`
  (`mem_lowerUnipotent_iff`).
* `eq_zero_of_nbar`: combine `exists_nbar_eq` with `eq_zero_of_eqOn_lowerUnipotent`.
