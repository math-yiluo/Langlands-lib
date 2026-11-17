# Polynomial test vectors on `O(n)` for real standard modules

Module: `Langlands.Representation.Archimedean.RealBlockTestVector`.

## Purpose and provenance

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealLinkedJacquetFunctionalInStagesStatement` (module
`RealLinkedJacquetInStagesProof`, through `RealSliceSurjective`). It builds explicit
polynomial functions in the matrix entries of `κ ∈ O(n)` and gives a criterion
(`exists_KF`) for when such a function is the restriction to `O(n)` of an `O(n)`-finite
function of the real standard module of a list `ds` of real blocks.

The construction is elementary. In the rows `b, b + 1` of a block, the complex coordinate
`Z_c = κ_{b,c} + i κ_{b+1,c}` turns under the left rotation `r_b(φ)` of that block by
`e^{iφ}`. So the block factor `Z_c^m Z_{c'} + Z̄_c^m Z̄_{c'}` has exactly the two Fourier
modes `±(m + 1)`. The criterion `exists_KF` combines the Library's extension theorem
`PrincipalSeriesExtension.principalSeriesExtension` with Worker 109's
`InductionStages.mem_realStandardModule_of_unitaryCompact` (module
`RealInductionStagesFourier`). The module makes no literature claim.

All declarations are in the namespace `Langlands.Archimedean.RealBlockTestVector`. `n` is
implicit throughout. For `hb : b + 1 < n`, the indices `ia hb = b` and `ib hb = b + 1` are
those of the Library's `RealBlockRotation`. `blockRotation n b φ` is the Library's left
rotation by `φ` in the rows `b, b + 1`. `expMode k φ = e^{ikφ}` and
`coeff k F = ∫₀^{2π} F(φ) e^{-ikφ} dφ` are from `RealBlockFourierFinite`.

## Declarations

### Entries of rotated matrices

- `rot_mul_ia`, `rot_mul_ib`: the rows `b` and `b + 1` of `r_b(φ) κ` are
  `cos φ κ_{b,c} - sin φ κ_{b+1,c}` and `sin φ κ_{b,c} + cos φ κ_{b+1,c}`.
- `rot_mul_of_ne`: the other rows of `r_b(φ) κ` are those of `κ`.

### The complex coordinates of a block

- `zp hb c κ = κ_{b,c} + i κ_{b+1,c}` and its conjugate `zm hb c κ = κ_{b,c} - i κ_{b+1,c}`.
- `expMode_one_eq`, `expMode_neg_one_eq`: `e^{±iφ} = cos φ ± i sin φ`.
- `zp_rot`, `zm_rot`: `Z_c(r_b(φ) κ) = e^{iφ} Z_c(κ)` and
  `Z̄_c(r_b(φ) κ) = e^{-iφ} Z̄_c(κ)`.
- `bf hb c c' m κ = Z_c^m Z_{c'} + Z̄_c^m Z̄_{c'}`, the block factor of degree `m + 1`.
- `expMode_pow_mul`: `e^{ikφ m} e^{ikφ} = e^{i(m+1)kφ}`.
- `bf_rot`: `bf(r_b(φ) κ) = e^{i(m+1)φ} Z_c^m Z_{c'} + e^{-i(m+1)φ} Z̄_c^m Z̄_{c'}`.
- `zp_rot_of_disjoint`, `zm_rot_of_disjoint`, `bf_rot_of_disjoint`: if the blocks `b`
  and `b'` are disjoint (`b + 1 < b'` or `b' + 1 < b`), the rotations of `b'` do not change
  `Z_c`, `Z̄_c` or the block factor of `b`.

### Two modes

- `coeff_two_mode N A B j`: the `j`-th Fourier coefficient of
  `φ ↦ e^{iNφ} A + e^{-iNφ} B` is `2π A [N = j] + 2π B [-N = j]`.
- `coeff_two_mode_eq_zero`: it vanishes when `|j| < |N|`.

### Signs

- `IsSignEq q F`: `F(diag(s) κ) = (∏ᵢ sᵢ^{qᵢ}) F(κ)` for every sign vector `s`
  (`sᵢ = ±1`) and every real matrix `κ`.
- `isSignEq_mul`, `isSignEq_pow`: exponents add under products and multiply under powers.
- `prod_pow_single`: `∏ⱼ sⱼ^{(Pi.single i m) j} = sᵢ^m`.
- `isSignEq_entry i c`: `κ ↦ κ_{i,c}` has exponent `Pi.single i 1`.
- `zp_diag`, `zm_diag`: the coordinates of `diag(s) κ`.
- `isSignEq_bf`: the block factor of degree `m + 1` has exponent `Pi.single b (m + 1)`.

### Translate-finiteness and continuity

- `isTranslateFinite_zp`, `isTranslateFinite_zm`, `isTranslateFinite_bf`: on the
  orthogonal group, these functions are translate-finite (`TranslateFinite.IsTranslateFinite`
  for the right translations by all of `O(n)`).
- `continuous_entry`, `continuous_zp`, `continuous_zm`, `continuous_bf`: continuity on real
  matrices.

### Test vectors

- `signReal_cases x`: `signReal x = 1 ∨ signReal x = -1`.
- `exists_KF` (**test vectors**): let `realRank ds = n`, and let
  `F : Matrix (Fin n) (Fin n) ℝ → ℂ` be continuous and translate-finite on `O(n)`, with
  `IsSignEq q F`. Suppose `(-1)^{qᵢ} = χ_{ds,i}(-1)` for the position characters of `ds`.
  Suppose also that for every induction block of `ds` of weight `m` at position `p`, and
  every `|k| < |m|` and orthogonal `κ`,
  `coeff k (φ ↦ F(r_p(φ) κ)) = 0`. Then there is `v` in
  `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` with
  `v(g) = F(g)` for every `g ∈ O(n)`.
- `coeff_eq_zero_of_two_mode`: if `F(r_p(φ) κ) = e^{iNφ} A(κ) + e^{-iNφ} B(κ)` for all
  `φ, κ`, then `coeff k (φ ↦ F(r_p(φ) κ)) = 0` for `|k| < |N|`.

## Proof notes

`exists_KF`: the sign hypothesis turns `IsSignEq q F` into the equivariance
`F(diag(sgn a) κ) = χ(sgn a) F(κ)` for the principal-series character of
`realPositionCharacter ds`, using `JacquetKernel.principalSeriesCharacter_sign`. The Library's
`principalSeriesExtension` then extends `F|_{O(n)}` to an `O(n)`-finite function `f` of the
principal series. The block Fourier coefficients of `f` at the induction blocks are
`coeff k (φ ↦ F(r_p(φ) κ))` (`blockFourierCoefficient_eq_coeff`), so they vanish for
`|k| < |m|`. Then `mem_realStandardModule_of_unitaryCompact` puts `f` in the standard module.
