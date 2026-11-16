# The Whittaker expansion from summable Whittaker terms

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionInduction`. This helper
module finishes half (E) of the Whittaker expansion. It is internal to this proof and not taken
from the literature. It is a column-by-column form of the standard Piatetski-Shapiro–Shalika
argument (see Cogdell 2004, proof of Theorem 1.1).

Notation. `F` is a number field, `ψ` is an additive character of `𝔸_F`, and
`f : GL_(r+1)(𝔸_F) → ℂ` is a function on the group-scheme points (`Points F (r + 1)`).
`P_j = projectionCoefficient F r j ψ f` is the library character coefficient along the subgroup
`Y_(r+1,j)` with the projection character. `G_j = whittakerSum F ψ f j` is the partial Whittaker
sum from module `ExpansionGSide`. Write `homeo = GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)`
for the library homeomorphism from the group-scheme points to the matrix group
`AdelicGL F (r + 1)`, the group on which the torus column framework works.

## Small lemmas (namespace `Langlands.Automorphic.CuspidalWhittaker`)

* `IsPeriodic.sub`: the difference of two `K^Idx`-periodic functions on `(𝔸_K)^Idx` is periodic.
* `fourierCoeff_sub` (with `𝔸_K/K` compact): for continuous periodic `f` and `g`, the torus
  Fourier coefficient of `f − g` at `a` is the difference of the coefficients. This is
  `torusIntegral_sub` applied to the products with `conj ψ₀(a · y)`.

## Base (namespace `Langlands.Global.RankinSelbergGlobal.Unfolding`)

* `projectionWeight_zero`: the projection weight at level `0` is the upper unipotent weight.
* `subgroupCharacterCoefficient_blockUnipotent_congr`: character coefficients along the block
  unipotent subgroups of two equal weights agree. The proof is `subst`.
* `projectionCoefficient_zero`: `P_0 = W_f`. At level `0` the subgroup `Y_(r+1,0)` is the upper
  unipotent subgroup `N_(r+1)`. The projection character is then the generic character with all
  coefficients `1`, so the coefficient is the library `whittaker F r ψ f`.

## P side

Assume from here on that `𝔸_F/F` is compact, `ψ` is a standard character, `f` is continuous and
left invariant under `GL_(r+1)(F)`, and `ψ = ψ₀(b ·)` with `ψ₀ = standardCharacter F`.

* `projTilde F ψ f j = P_j ∘ homeo.symm`. This is `P̃_j`, the projection coefficient as a
  function on the matrix group.
* `projTilde_top`: `P̃_r = f ∘ homeo.symm`. This is the library `projectionCoefficient_top`.
* `character_colVec_colPoint`: on the column point `u_(j+1)(y)`, the projection character at
  entry `(j, j+1)` is the column character `ψ₀(b y_j)`. This lemma needs only `ψ = ψ₀(b ·)`.
* `colCoeffB_projTilde` (column step): let `j < r`, and assume `P̃_(j+1)` has the properties
  `LevelPropsB (j + 1)` of module `ColumnsB`. Then the column coefficient of `P̃_(j+1)` at the
  character `ψ₀(b y_j)` is `P̃_j`. The library `projectionCoefficient_eq_column` writes `P_j` as
  the normalized period of the twisted `P_(j+1)` over a fundamental domain of the column
  subgroup. The bridge `normalized_setIntegral_column_eq_torusIntegral` (module `ColumnTorus`)
  turns this period into a torus integral. Continuity and periodicity of the integrand come from
  `LevelPropsB (j + 1)`. The torus integral is the column coefficient `colCoeffB`, after
  `symm_colUnit_mul` and `character_colVec_colPoint`.
* `levelPropsB_projTilde` (downward induction): assume `LevelPropsB r (f ∘ homeo.symm)`. Then
  `P̃_c` satisfies `LevelPropsB c` for every `c ≤ r`. The induction runs on `d = r − c`. The step
  writes `P̃_c` as the column coefficient of `P̃_(c+1)` (`colCoeffB_projTilde`) and applies
  `LevelPropsB.step`.

## Expansion

Assume moreover `LevelPropsB r (f ∘ homeo.symm)` (`htop`). Also assume, for every `k ≤ r` and
every `x`, that `q ↦ ‖W_f(diag(q.out, I) x)‖` is summable over `N_k(F) \ GL_k(F)` (`hsum`).

* `projTilde_eq_whittakerSumGL` (upward induction): for `b ≠ 0` and every `j ≤ r`,
  `P̃_j = G̃_j`, where `G̃_j = whittakerSumGL F ψ f j = G_j ∘ homeo.symm`.
  The case `j = 0` is `projectionCoefficient_zero` with `whittakerSum_zero`. For the step
  `j → j + 1` with `j < r`, apply the uniqueness lemma `eq_zero_of_colCoeffB_eq_zero` (module
  `ColumnsB`) to `H = P̃_(j+1) − G̃_(j+1)`. Its hypotheses hold as follows.
  - Continuity and periodicity along column `j + 1`. For `P̃_(j+1)` they come from
    `LevelPropsB (j + 1)`. For `G̃_(j+1)` they are `continuous_whittakerSumGL_col` (which uses
    `hsum` at `k = j + 1`) and `isPeriodic_whittakerSumGL_col`.
  - Invariance under rational block matrices of size `j + 1`. For `P̃_(j+1)` it comes from
    `LevelPropsB (j + 1)`. For `G̃_(j+1)` it is `whittakerSumGL_rational_mul`.
  - The zeroth column Fourier coefficient of `H` vanishes. For `P̃_(j+1)` this is
    `fourierCoeff_zero_of_blockVanishing`. For `G̃_(j+1)` it is
    `fourierCoeff_zero_whittakerSumGL_col`. Combine them with `fourierCoeff_sub`.
  - The column coefficient of `H` at `ψ₀(b y_j)` vanishes. By `colCoeffB_sub` it is
    `colCoeffB P̃_(j+1) − colCoeffB G̃_(j+1)`. This equals `P̃_j − G̃_j` by
    `colCoeffB_projTilde` and the step identity `colCoeffB_whittakerSumGL`. That difference is
    zero by the induction hypothesis.
  So `H = 0`.
* `hasSum_whittaker_of_levelPropsB` (the expansion): under the hypotheses of this section,
  for every `x`,
  `HasSum (q ↦ W_f(cornerAdelicPoint F r q.out * x)) (f x)` over `N_r(F) \ GL_r(F)`.
  Write `ψ = ψ₀(b ·)` with `b ≠ 0` (library `exists_eq_standardCharacter_mul`). Evaluate
  `projTilde_eq_whittakerSumGL` at `j = r` and `homeo x`. The left side is `f x` by
  `projTilde_top`, and the right side is the `tsum` defining `G_r(x)`. The family is summable
  by `hsum` at `k = r`, so its `tsum` is its sum. Finally `diag(q, 1)` is
  `cornerAdelicPoint F r q` (library `padRational_eq_cornerAdelicPoint`).
