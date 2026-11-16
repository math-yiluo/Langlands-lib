# Rational points, the mirabolic subgroup and the kernel of the equal-rank unfolding

This is an internal helper module for `EqualUnfoldingReduction.md`. Provenance: internal. It
collects the group-theoretic facts about `GL_n(F) ⊂ GL_n(𝔸)`, `n = r + 1`, that the
equal-rank unfolding of Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.3,
printed p.210, uses without comment. It also defines the kernel that every step integrates.
All declarations live in namespace `Langlands.Global.RankinSelbergGlobal.EqualUnfolding`.

Notation: `Points F n` is `GL_n(𝔸)` and `RationalGL F n` is `GL_n(F)`. The Library's
`rationalPoint F n g` is the image of `g` in `GL_n(𝔸)`. `unipotentRationalImage F n` is
`N_n(F)` inside `GL_n(𝔸)`. `lastRow F r x` is the last row `e_n x`.

The two local instances `equalKernelSchemeAffine` and `equalKernelSchemeSmooth` restate the
published `GroupScheme.GeneralLinear.isAffine_groupScheme` and
`GroupScheme.GeneralLinear.smoothStatement` for `Scheme F n`, as the local instances of the
Library's `EqualUnfoldingStatement` do.

## Rational points (`RationalPoints`)

- `rationalPointHom`: `g ↦ rationalPoint F n g`, bundled as a monoid homomorphism
  `GL_n(F) →* GL_n(𝔸)`. The lemmas `rationalPoint_mul`, `rationalPoint_inv` and
  `rationalPoint_one` follow from it.
- `rationalPoint_injective` holds. `rationalPoint_mem_rationalSubgroup` says the image lies in
  the Library's `AdelicGroupPoints.rationalSubgroup`, and `exists_rationalPoint_eq` says every
  point of that subgroup is a rational point.
- `rationalPoint_mem_unipotentRationalImage_iff`: `rationalPoint g ∈ N_n(F)` exactly when `g`
  is upper unitriangular.

## The mirabolic subgroup (`Mirabolic`)

- `mirabolicRationalImage F r`: `P_n(F)`, the image of the Library's
  `GeneralLinear.mirabolic r F` (last row `e_n`) under `rationalPointHom`. It lies in `GL_n(F)`
  (`mirabolicRationalImage_le`), is discrete (`isDiscrete_mirabolicRationalImage`) and contains
  `N_n(F)` (`unipotentRationalImage_le_mirabolicRationalImage`). Membership of rational points
  is characterized by `rationalPoint_mem_mirabolicRationalImage_iff`.
- `mem_rationalUpperUnipotent_iff`: `N_r(F)` is the upper unitriangular subgroup of `GL_r(F)`.
- `cornerAdelicPoint_eq` and `cornerAdelicPoint_mem_mirabolicRationalImage`: the Library's
  corner point `diag(a, 1)` is the rational point of the Levi element, so it lies in `P_n(F)`.
- `val_mem_upperUnipotent_iff`: a mirabolic matrix is upper unitriangular exactly when its
  upper-left `r × r` block is.
- `existsUnique_cornerAdelicPoint`: every `p ∈ P_n(F)` lies in exactly one coset
  `N_n(F) diag(γ, 1)`, where `γ` runs over the chosen representatives `q.out` of
  `N_r(F) \ GL_r(F)` (the Library's `UnipotentRationalCosets F r`). The proof shows that
  `p diag(a, 1)⁻¹ ∈ N_n(F)` exactly when `π(p) a⁻¹ ∈ N_r(F)`, where `π` is the Library's
  `GeneralLinear.Mirabolic.projection` to the upper-left block. So the unique coset is the class
  of `π(p)`. This is the decomposition `P_n(F) = ⊔_γ N_n(F) diag(γ, 1)` behind the Fourier
  expansion step on p.210.
- `lastRow_mirabolic_mul` and `lastRow_unipotent_mul`: left multiplication by `P_n(F)` or by
  `N_n(𝔸)` does not change the last row. `continuous_lastRow` holds.

## The kernel (`Kernel`)

`equalKernel F f f' Φ s x = f(x) f'(x) Φ(e_n x) |det x|^s`, using the Library's `detPower`.
With two cusp forms it is the integrand over `P_n(F) \ GL_n(𝔸)` after the Eisenstein step. With
a Whittaker function and a cusp form it is the integrand over `N_n(F) \ GL_n(𝔸)`. With two
Whittaker functions it is the Library's `equalWhittakerIntegrand` at a representative
(`equalWhittakerIntegrand_eq`, by `rfl`). `measurable_equalKernel` gives measurability from
the measurability of `f`, `f'` and `x ↦ Φ(e_n x)`.
