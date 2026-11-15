# The expansion of the projection from the Whittaker expansion of cusp forms

Module `Langlands.Global.RankinSelberg.ProjectionExpansion`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. It proves premise E,
`ProjectionWhittakerExpansion`, of the published `UnequalUnfoldingReductionStatement`, assuming
`CuspidalWhittakerExpansion`, the Whittaker expansion of the cusp forms of the realization.

Provenance: derived. Cogdell 2004 (source `cogdell-2004-analytic-theory-gln`, §2.2, printed
p.205, PDF p.208) states the expansion of `P^n_m φ` and obtains it from the Fourier expansion of
cuspidal functions on mirabolic subgroups (§1). The implemented proof is internal and different:
it integrates the Whittaker expansion of `φ` on `GL_n` over one column of `Y_(n,m)` at a time.

Notation: `n = r + 1`, `φ = cuspFunction F T v`, `W = cuspWhittaker F T ψ v` for a standard
`ψ`, and `diag(γ, I)` is the padding of `γ ∈ GL_k(F)`, `padRational F _ γ`.

## Definitions

- `CuspidalWhittakerExpansion F T`: for every standard `ψ`, vector `v` and `g ∈ GL_n(𝔸)`, the
  family `q ↦ W(cornerAdelicPoint F r q.out · g)` over `UnipotentRationalCosets F r`
  (`N_r(F) \ GL_r(F)`) is absolutely summable (norms summable) and has sum `φ(g)`. This is part
  1 of the Library's `WhittakerExpansionStatement` with all `m_i = 1`, for the realization's
  cusp forms (Cogdell 2004, Theorem 1.1).
- `projectionCoefficient F r j ψ f x` is the Library's `subgroupCharacterCoefficient` along
  `Y_(r+1,j) = projectionUnipotent F (r + 1) j`, with `projectionCharacter F r j ψ`. For
  `j = t + 1` this is the coefficient used in `projection`.
- `columnUnipotent F r j` is the block Levi part `V_(j+1)` of `Y_(r+1,j)` relative to
  `Y_(r+1,j+1)`: the column `j + 1` above row `j + 1`. `colVec` reads off that column, and
  `colPoint c` is the point `1 + colMatrix j c`.
- `columnTwist F hj ψ g x = ψ((P c)_j) · conj ψ(c_j)`, where `P = diag(g, I)` for
  `g ∈ GL_(j+1)(F)` and `c` is the column vector of `x`.
- `LastRowStandard F g`: the last row of `g ∈ GL_(k+1)(F)` is that of the identity.
- `cosetPad F j : N_j(F) \ GL_j(F) → N_(j+1)(F) \ GL_(j+1)(F)` is `γ ↦ diag(γ, 1)`.
- `rationalCosetIndexEquiv F m` identifies the Points-level index type `RationalCosetIndex F m`
  of premise E with `UnipotentRationalCosets F m`. It is induced by `rationalSubgroupEquiv`,
  the identification of the rational subgroup of `GL_m(𝔸)` with `GL_m(F)`.

## The induction

For `t + 1 ≤ j ≤ r` the claim is that, for every `x`,
`q ↦ W(diag(γ_q, I) x)` over `N_j(F) \ GL_j(F)` has sum `projectionCoefficient F r j ψ φ x`.

- **Top** (`projectionCoefficient_top`): `Y_(r+1,r)` is trivial, so its coefficient is
  evaluation. `padRational_eq_cornerAdelicPoint` and `CuspidalWhittakerExpansion` give the claim
  for `j = r`.
- **One column** (`projectionCoefficient_eq_column`): by `subgroupCharacterCoefficient_eq_levi`
  with `e = e_j`, `w = e_(j+1)`, the coefficient along `Y_(r+1,j)` is the normalized period
  over `V_(j+1)` of `conj ψ(c_j(m)) · projectionCoefficient F r (j+1) ψ φ (m x)`.
  `projectionCharacter_leviInclusion` identifies the character on `V_(j+1)`. Compactness of all
  quotients comes from `compactSpace_projectionRationalQuotient` and
  `compactSpace_columnRationalQuotient`.
- **Twisting** (`padRational_mul_column`, `cuspWhittaker_colPoint_mul`):
  `diag(γ, I) · m = colPoint(P c) · diag(γ, I)`, and `W(colPoint d · z) = ψ(d_j) W(z)`. Hence the
  expanded integrand is `Σ_q columnTwist(γ_q)(m) · W(diag(γ_q, I) x)`.
- **Exchange** (`hasSum_projectionCoefficient_step`): `|columnTwist| = 1`, so the terms are
  dominated by the summable constants `‖W(diag(γ_q, I) x)‖`. `hasSum_integral_of_dominated_convergence`
  exchanges sum and integral; no local uniformity is needed.
- **Orthogonality** (`normalized_setIntegral_columnTwist`): the normalized period of
  `columnTwist(g)` over `V_(j+1)` is `1` if `LastRowStandard g` (`columnTwist_eq_one`) and `0`
  otherwise. In the second case `exists_columnTwist_ne_one` gives a point where the character is
  not `1`, and `setIntegral_fundamentalDomain_character_eq_zero` (module `ProjectionPeriod`)
  applies. It uses the right invariance of Haar measure on `V_(j+1)(𝔸)`
  (`haar_isMulRightInvariant_of_compactRationalQuotient`).
- **Cosets** (`hasSum_projectionCoefficient_succ`): the surviving cosets, those with standard
  last row, are exactly the image of the injective map `cosetPad` (`cosetPad_injective`,
  `lastRowStandard_out_iff`). `exists_unitriangular_mul_padGL` writes `g = n · diag(g', 1)`,
  with `n` unitriangular and `g'` invertible because its determinant equals `det g`
  (`Matrix.det_succ_row`). `W(diag(γ, I) x)` depends only on the coset of `γ`
  (`cuspWhittaker_padRational_of_rightRel`), and `diag(diag(γ', 1), I) = diag(γ', I)`
  (`padRational_padGL`). `Function.Injective.hasSum_iff` reindexes the sum.
- `hasSum_projectionCoefficient` assembles the downward induction from `j = r`.

## Main theorem

`projectionWhittakerExpansion_of_cuspidalWhittakerExpansion F h T hT :
ProjectionWhittakerExpansion F h T`. Apply the claim at `j = t + 1` and `x = diag(g, I)`, and
reindex by `rationalCosetIndexEquiv`. Then `diag(ρ_q g, I) = diag(γ_q, I) diag(g, I)`
(`pad_mul`, `pad_coe_rationalSubgroup`), with `γ_q` a representative of the corresponding coset
(`cuspWhittaker_padRational_of_rightRel`). Finally unfold `projection`: `pad_pad` and
`detPower_pad` come from the Library module `UnequalAnalyticPoints`, and `HasSum.mul_left`
supplies the factor `|det g|^{-(n-m-1)/2}`.

The module also records `rationalGLCountable`: `GL_k(F)` embeds into the discrete rational
subgroup of `GL_k(𝔸)` and is therefore countable.
