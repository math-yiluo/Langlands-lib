# Complex determinant twists of real standard modules

Module `Langlands.Representation.Archimedean.RealStandardComplexTwist`, namespace
`Langlands.Archimedean.RealComplexTwist`.

Internal helper results on `GL_n(ℝ)`, used for the twist rule of real-place parameters under
complex powers of the norm (module `Langlands.Automorphic.RealPlaceParameterNormPowerTwist`).
They extend the published real-exponent constructions `realBlockTwist` (module
`RealLinkedJacquetPairReduction`), `RealLinkedJacquetStages.twK` (module
`RealLinkedJacquetInStagesProof`) and `RealTemperedTwist.twistEquiv` (module
`RealTemperedTwist`) to a complex exponent `s`; the proofs are the same computations. No source
is cited and nothing is assumed: every statement is proved.

Notation. `|det g|^s` is `RealLinkedJacquetStages.detPow n s g = (|det g| : ℂ) ^ s` for complex
`s`. `KFin n ds` is the space of `O(n)`-finite functions of the real standard module
`realStandardModule n ds` of a list `ds` of real blocks (the same space as
`Automorphic.realStandardKFinite n ds`). `R_k f (g) = f(g k)` is
`Whittaker.rightTranslation`, and `R_X f` is the right derivative
`rightDerivative (matrixModel ℝ n) X f` along a real matrix `X`.

## Definitions

- `realBlockComplexTwist c x`: the real block `x` with the complex number `c` added to its
  exponent. A character block `sgn^e |·|^t` becomes `sgn^e |·|^(t + c)`
  (`RealJacquetFrobenius.charData`); an induction block of the complex character of weight `m`
  and exponent `t` becomes the one of weight `m` and exponent `t + c`
  (`characterOfParams`). `realBlockComplexTwist_ofReal`: for real `c` this is the published
  `realBlockTwist c`.
- `detPowK hχ hind`: multiplication by `|det|^s` from `KFin r ds` to `KFin r es`, for lists
  `ds`, `es` whose position characters satisfy `χ_es(x) = χ_ds(x) |x|^s` (`hχ`) and whose
  induction blocks have the same weights (`hind`).
- `twistEquiv s ds hr`: for `realRank ds = n`, the complex-linear equivalence
  `KFin n ds ≃ KFin n (ds.map (realBlockComplexTwist s))` given by multiplication by
  `|det|^s`, with inverse multiplication by `|det|^(-s)`.

## Results

- `realBlockComplexTwist_rank`, `realRank_map_realBlockComplexTwist`: twisting keeps block
  ranks and the total rank.
- `realPositionCharacter_map_complexTwist`: at every position inside the list, the position
  character of the twisted list is that of `ds` times `|x|^s`.
  `realInducedBlockAt_map_complexTwist`: the induction blocks of the twisted list are those of
  `ds` with exponent shifted by `s`, of the same weights.
- `detPowMul_mem_realStandardModule`: under `hχ` and `hind`, multiplication by `|det|^s` maps
  `realStandardModule r ds` into `realStandardModule r es`. Smoothness is that of a product
  (`contMDiff_mul_fun`, `contMDiff_detPow`). The principal-series transformation law gains the
  factor `∏ |a_j|^s = |det(diag(a) u)|^s`, since `|det u| = 1` for upper unipotent `u`
  (`detPow_of_mem_upperUnipotent`, `detPow_diagonalUnits`). The vanishing Fourier coefficients
  along the rotations of the induction blocks are kept, because `|det|^s` is `1` on the
  rotations (`blockFourierCoefficient_detPowMul`). `O(n)`-finiteness is preserved by the
  published `detPowMul_mem_kFiniteVectors`.
- `twist_char`, `twist_ind`, `untwist_char`, `untwist_ind`: the hypotheses of `detPowK` for the
  pair (`ds`, twisted list) in both directions; `twistEquiv_apply`, `twistEquiv_symm_apply`.
- `twistEquiv_symm_rightTranslation`: for `k ∈ O(n)`, the inverse twist of `R_k f` is
  `R_k` of the inverse twist of `f`, since `|det k| = 1` (`detPow_of_mem_unitaryCompact`).
- `twistEquiv_lie`: for a real matrix `X`,
  `R_X(|det|^s f) = |det|^s R_X f + c_X |det|^s f` with
  `c_X = R_X(|det|^s)(1)`, written with `realStandardLie`. The proof is the product rule
  `RealPrincipalSeriesDuality.rightDerivative_mul_fun` and
  `RealTemperedTwist.rightDerivative_detPow` (`R_X(|det|^s)(g) = |det g|^s c_X`).
- `twistEquiv_symm_rightDerivative`: the same identity read through the inverse,
  `|det|^(-s) R_X f = R_X(|det|^(-s) f) + c_X |det|^(-s) f` for `f` in the twisted module,
  with the same `c_X = R_X(|det|^s)(1)`.

The scalar `c_X` is not computed; only its independence of the point is used.
