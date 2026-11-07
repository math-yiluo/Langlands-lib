# Column Fourier coefficients of automorphic functions

Author: Worker 1709.

This is internal infrastructure for the proof of
`Langlands.Automorphic.CuspidalUnitaryLocalGenericityStatement`. It implements one step of the
classical construction of the Whittaker coefficient of a cusp form on `GL_{r+1}`, integrating
over one column of the upper unipotent group at a time. The route is the standard argument for
the nonvanishing of Whittaker coefficients of cusp forms (Piatetski-Shapiro, Shalika). The Lean
statements and proofs are this module's own, written with explicit iterated integrals, and no
source is cited for them. All results are proved, with no hypothesis beyond
`CompactSpace (AdeleQuotient K)`.

Matrices are indexed by `Fin (r + 1)` (0-indexed). Torus integrals over `(𝔸_K / K)^{r+1}` or
`(𝔸_K / K)^{(r+1)×(r+1)}` carry dummy coordinates that the integrand ignores. Since the Haar
measure is a probability measure, those coordinates do not change the value.

## Rational changes of variables

`ratMulVec B` multiplies adelic vectors by a rational matrix. It preserves rational vectors, it
is continuous, and it is surjective for invertible `B`. `fourierCoeff_ratMulVec` states, for
`g ∈ GL_ι(K)` and continuous periodic `f`, that the coefficient of `w ↦ f(g w)` at `b g` is the
coefficient of `f` at `b`.

## Level properties

Let `F : GL_{r+1}(𝔸_K) → ℂ`.

- `MirInvariant c F`: `F(γ g) = F(g)` for every rational `γ` with `IsMir c γ`, i.e. `γ` is the
  identity in the rows `≥ c` and the columns `> c`.
- `BlockVanishing c F`: for `1 ≤ m ≤ c` and every `g`,
  `∫_X F(blkUnit m c X · g) dX = 0`. Here `X` runs over the block `i < m ≤ j ≤ c`.
- `superSum c u = Σ_{i ≥ c} u_{i,i+1}`.
- `Equivariant c F`: `F(u g) = ψ(superSum c u) F(g)` for `u` with `IsUpperColId c u`, i.e.
  upper unitriangular with columns `≤ c` equal to those of the identity.

## The column coefficient

For `c < r`, `colCoeff c F g` is the Fourier coefficient of `y ↦ F(colUnit (c+1) y · g)` at the
character `y ↦ ψ(y_c)`:

```text
colCoeff c F (g) = ∫ F(u_{c+1}(y) g) conj(ψ(y_c)) dy.
```

Here `u_{c+1}(y)` has entries `y_i` at `(i, c+1)` for `i ≤ c`. For `c ≥ r` the definition
returns `F g`, a value that is never used. `MirInvariant (c+1) F` makes the integrand periodic
(`isPeriodic_col`). Under continuity, `colCoeff c F` is continuous (`continuous_colCoeff`, via
`continuous_torusIntegral`). It is additive, homogeneous, and commutes with right translation.

## The four steps

Assume `c < r`, that `F` is continuous, and that `MirInvariant (c + 1) F` holds.

1. **Invariance** (`mirInvariant_colCoeff`). `colCoeff c F` is `Mir(c)`-invariant. A rational
   `γ` with `IsMir c γ` satisfies `IsBlk (c+1) γ` and normalizes the column group:
   `u_{c+1}(y) γ = γ u_{c+1}(γ⁻¹ y)`. Its row `c` is the unit vector, so the change of
   variables `y ↦ γ⁻¹ y` fixes the character.
2. **Equivariance** (`equivariant_colCoeff`). From `Equivariant (c + 1) F` we get
   `Equivariant c (colCoeff c F)`. Write `u = u_{c+1}(y₀) u'`, where `u'` has trivial column
   `c + 1` (`isUpperColId_peel`). Conjugating `u'` past `u_{c+1}(y)` keeps the rows `≥ c+1`
   (`isUpperColId_conj`), and translating `y` by `y₀` produces the factor
   `ψ(u_{c,c+1})`. Then `superSum c u = superSum (c+1) u + u_{c,c+1}` (`superSum_succ`).
3. **Cuspidality** (`blockVanishing_colCoeff`). From `BlockVanishing (c + 1) F` we get
   `BlockVanishing c (colCoeff c F)`. For `1 ≤ m ≤ c` the proof has three parts.
   - Step A: the character is invariant under translation by `trunc_m z` because
     `(trunc_m z)_c = 0`. Averaging over `z`, and using the splitting identity
     `colUnit_mul_blkUnit_split`, rewrites `colCoeff c F (b_{m,c}(X) g₀)` as
     `∫_y χ(y) Ψ(X, y)`. Here `Ψ(X, y)` integrates `F` over block width `c + 1` with column
     `c + 1` replaced (`colUnit_truncVec_mul_blkUnit`, `blkUnit_updateCol_mul_colUnit`).
   - Step B: Fubini (`torusIntegral_comm`) exchanges `X` and `y`.
   - Step C: `torusIntegral_updateCol` integrates out the replaced column, and the result is
     a block integral of width `c + 1`, which vanishes by hypothesis.
4. **Nonvanishing** (`eq_zero_of_colCoeff_eq_zero`). If moreover
   `BlockVanishing (c + 1) F` holds and `colCoeff c F ≡ 0`, then `F ≡ 0`. By Fourier
   uniqueness (`eq_zero_of_fourierCoeff_eq_zero`), it suffices that every Fourier coefficient
   `a ∈ K^{r+1}` of `y ↦ F(u_{c+1}(y) g)` vanishes. There are four cases.
   - If `a_i ≠ 0` for some dummy coordinate `i ≥ c + 1`, the function ignores `y_i` while the
     character does not. Translation by a point where `ψ ≠ 1` (`exists_adelicCharacter_ne_one`)
     shows that the coefficient is zero.
   - If `a = 0`, the coefficient is the block integral with `m = c + 1`, which equals the
     column integral (`blkUnit_eq_colUnit` with the projection `colProj`). It vanishes by
     `BlockVanishing (c + 1) F`.
   - If `a_c ≠ 0`, take the rational lower triangular `δ` with row `c` equal to `a` on the
     coordinates `≤ c`, and identity elsewhere. Then `IsBlk (c+1) δ`, so also
     `IsBlk (c+1) δ⁻¹`. For a rational block matrix `β`, `fourierCoeff_col_transform` sends
     the coefficient at `a` of `y ↦ F(u_{c+1}(y) g)` to the coefficient at `a β` of
     `y ↦ F(u_{c+1}(y) β⁻¹ g)`. Apply it with `β = δ⁻¹`. Since `a = e_c δ`, we get
     `a δ⁻¹ = e_c`, so the coefficient at `a` becomes the coefficient of `F(· δ g)` at the
     unit vector `e_c`. That is `colCoeff c F (δ g) = 0`.
   - If `a_c = 0` but `a_k ≠ 0` for some `k < c`, a rational transvection reduces to the
     previous case.

`MirInvariant.mono` and the fact that `IsMir c` implies `IsMir (c + 1)` let the hypotheses
pass between levels.
