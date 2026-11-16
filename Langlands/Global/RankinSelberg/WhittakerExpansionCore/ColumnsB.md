# Column coefficients at the character `ψ₀(b y_c)`

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.ColumnsB`, namespace
`Langlands.Automorphic.CuspidalWhittaker`. A helper module for half (E) of the Whittaker
expansion. It is internal to this proof, not taken from the literature. It adapts the library
column framework `Automorphic.CuspidalWhittaker.Columns`, which uses the character
`y ↦ ψ₀(y_c)`, to the character `y ↦ ψ₀(b y_c)` for a fixed `b ∈ K`. Here `ψ₀` is
`adelicCharacter K`. This is needed because a general standard character has the form
`ψ = ψ₀(b ·)`. Most proofs are copies of the library proofs with `1` replaced by `b`.

Throughout, `F : GL_(r+1)(𝔸_K) → ℂ` is a function on the library matrix group `AdelicGL`, and
`c < r` is a column index (`h : c < r`).

## Definitions

* `colCoeffB h b F g = fourierCoeff (y ↦ F(colUnit (c+1) y · g)) (Pi.single c b)`, that is,
  `∫_{(𝔸/K)^(r+1)} F(u_(c+1)(y) g) conj(ψ₀(b y_c)) dy`.
* `LevelPropsB c F`: `F` is continuous, `Mir(c)`-invariant (`MirInvariant c`) and has vanishing
  block integrals (`BlockVanishing c`). This is the library `LevelProps` without the
  equivariance field.

## Results

* `continuous_colCoeffB`, `mirInvariant_colCoeffB`, `blockVanishing_colCoeffB`: copies of the
  library continuity, invariance and cuspidality steps. In the invariance step the row identity
  becomes `vecMul (Pi.single c b) γ = b • (row c of γ) = Pi.single c b`
  (`Matrix.single_vecMul`). In the cuspidality step, `ψ₀(b z_c) = 1` when `z_c = 0`.
* `LevelPropsB.step`: `LevelPropsB (c+1) F → LevelPropsB c (colCoeffB h b F)`.
* `LevelProps.levelPropsB`: the library `LevelProps` implies `LevelPropsB`. With the library
  `levelProps_top` this gives the starting level `r` for a cuspidal continuous
  rational-left-invariant function.
* `colCoeffB_sub`: the coefficient of `F₁ − F₂` is the difference of the coefficients, if both
  functions are continuous and periodic along the column (`torusIntegral_sub`).
* `fourierCoeff_zero_of_blockVanishing`: under `Mir(c+1)`-invariance and `BlockVanishing (c+1)`,
  the zeroth Fourier coefficient along column `c+1` vanishes. This is the library `case0`
  argument: the block `m = c + 1` at level `c + 1` is the column `c + 1`
  (`blkUnit_eq_colUnit`, `torusIntegral_comp` along `colProj`).
* `fourierCoeff_col_transform_of`: the library `fourierCoeff_col_transform` with weaker
  hypotheses. It needs only continuity and periodicity of `y ↦ F(u_(c+1)(y) g)` for every `g`,
  and invariance of `F` under left multiplication by rational block matrices `β` with
  `IsBlk (c+1) β`.
* `eq_zero_of_colCoeffB_eq_zero hb …`: let `b ≠ 0`. Assume `F` satisfies the three hypotheses
  of the previous item, and the zeroth Fourier coefficient along column `c+1` vanishes at every
  `g` (`h00`). If `colCoeffB h b F` vanishes identically, then `F = 0`.

## Proof of the nonvanishing step

This is the library proof of `eq_zero_of_colCoeff_eq_zero`, with two changes. It shows that every
Fourier coefficient `â(a)` of `y ↦ F(u_(c+1)(y) g)` vanishes, then applies Fourier uniqueness
(`eq_zero_of_fourierCoeff_eq_zero`) at `y = 0`.

1. If `a_i ≠ 0` for some `i ≥ c + 1`, translate by `Pi.single i (a_i⁻¹ x₀)` with `ψ₀(x₀) ≠ 1`.
   The function does not see coordinates `≥ c + 1` (`colUnit_congr`). So `â(a)` is unchanged
   but also multiplied by `conj ψ₀(x₀) ≠ 1`, hence it is `0`.
2. If `a` is supported in rows `≤ c` and `a_c ≠ 0`: let `δ` be the identity with row `c`
   replaced by `b⁻¹ a`. It is lower triangular with determinant `b⁻¹ a_c ≠ 0`, and a block
   matrix of size `c + 1`. Then `a = vecMul (Pi.single c b) δ`. So the transformation rule
   moves `â(a)` to the coefficient at `Pi.single c b` of a left translate, which is a value of
   `colCoeffB h b F` and vanishes. This is the first change: the library uses `a` itself as
   row `c`.
3. If `a = 0`, use `h00`. This is the second change: the library derives it from block
   vanishing.
4. If `a ≠ 0` is supported in rows `< c`, a rational transvection reduces to case 2.
