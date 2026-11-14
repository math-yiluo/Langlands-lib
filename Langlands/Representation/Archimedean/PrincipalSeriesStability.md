# `K`-finite principal-series functions are stable under `K` and `𝔤`

Module: `Langlands.Representation.Archimedean.PrincipalSeriesStability`.

## Purpose and provenance

This module is internal infrastructure for proving the existence halves of the Langlands
classification for `GL_n` over an archimedean field in the Library's algebraic form:
`Langlands.Archimedean.ComplexLanglandsQuotientStatement` (`F = ℂ`, `K = U(n)`) and
`Langlands.Archimedean.RealLanglandsQuotientStatement` (`F = ℝ`, `K = O(n)`). Both statements ask
for an intertwiner from the `K`-finite functions of a standard module, and that space is only a
`(𝔤, K)`-module if it is closed under right translation by `K` and under the right derivatives
`rightDerivative (matrixModel F N) X` for `X ∈ 𝔤𝔩_N(F)`. This module proves both closure
properties for the Library's smooth principal series `principalSeries F N χ` over any `RCLike F`.
For `F = ℂ` it then specializes them to `complexStandardModule n ds` with `K = unitaryCompact ℂ n`.

The mathematics is standard. A smooth induced representation is stable under right translation
and under the derived action of the Lie algebra, and the derived action of `𝔤` preserves
`K`-finite vectors because `Ad(k)` acts on the finite-dimensional space `𝔤`. This is textbook
background on admissible representations (for example Knapp, *Representation Theory of
Semisimple Groups: An Overview Based on Examples*, Chapter VIII). The module makes no literature
assertion beyond these elementary facts about the Library definitions `principalSeries`,
`kFiniteFunctions`, `kFiniteVectors`, `rightDerivative` and `Whittaker.rightTranslation`, so it
cites no literature sources. The coordinate function `unitsExtension` is an auxiliary device of
this formalization and does not appear in the literature.

Throughout, `F` is an `RCLike` field (`ℝ` or `ℂ`), `N` is a natural number,
`Langlands.GeneralLinear N F` is `GL_N(F)` with the Library's manifold structure
`matrixModel F N`, and smooth means `ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞`.

## Proof route

The proofs work in matrix coordinates. `GL_N(F)` is an open subset of the real vector space
`M_N(F)` of matrices, so a function `f` on `GL_N(F)` extends by `0` to a function `unitsExtension f`
on all matrices, and this extension is smooth on the open set of invertible matrices. Manifold
derivatives of `f` become ordinary Fréchet derivatives of the extension. In particular

`(R(X) f)(g) = D(unitsExtension f)(g) (g X)`,

so `R(X) f` is smooth, and the right derivative is additive and complex-homogeneous in `f` and
real-linear in `X`. A chain-rule computation gives the conjugation formula
`R(k) (R(X) f) = R(k X k⁻¹) (R(k) f)`.

For `K`-finiteness, let `f` be `K`-finite and let `W` be the finite-dimensional span of the
translates `R(k) f`, `k ∈ K`. Fix a real basis `b_1, …, b_m` of `M_N(F)`. By the conjugation
formula and linearity in `X`, every translate `R(k) (R(X) f)` lies in the sum of the images of `W`
under the complex-linear maps `R(b_i)`. That sum is finite-dimensional.

Membership in the principal series is checked directly. Right translation commutes with the left
equivariance condition `f(a u g) = χ(a) f(g)`. For right derivatives, the identity
`f(a g h) = c f(g h)` for all `h` differentiates in `h` at `h = 1`.

## Declarations

All declarations are in the namespace `Langlands.Archimedean`.

### Functions on `GL_N(F)` in matrix coordinates

- `unitsExtension φ y` (definition): for `φ : GL_N(F) → ℂ` and a matrix `y`, this is `φ y` if `y`
  is invertible and `0` otherwise.
- `unitsExtension_val`: `unitsExtension φ g = φ g` for `g ∈ GL_N(F)`.
- `unitsExtension_of_not_isUnit`: the extension vanishes at non-invertible matrices.
- `unitsExtension_add`, `unitsExtension_smul`: the extension is additive and complex-homogeneous
  in `φ`.
- `unitsExtension_rightTranslation`: the extension of `g ↦ φ(g k)` is `y ↦ unitsExtension φ (y k)`.
- `isOpen_setOf_isUnit_matrix`: the invertible matrices form an open set.
- `range_val_eq_setOf_isUnit`: the image of `GL_N(F)` in `M_N(F)` is the set of invertible
  matrices.
- `mfderiv_units_val`: the manifold derivative of the inclusion `GL_N(F) → M_N(F)` is the identity.
- `mfderiv_eq_fderiv_of_eq_comp`: if `φ g = ψ g` for all `g ∈ GL_N(F)` and `ψ` is differentiable at
  `x`, then the manifold derivative of `φ` at `x` equals the Fréchet derivative of `ψ` at `x`.
- `contDiffOn_unitsExtension`: if `φ` is smooth, then `unitsExtension φ` is `C^∞` on the invertible
  matrices.
- `differentiableAt_unitsExtension`: if `φ` is smooth, then `unitsExtension φ` is differentiable at
  every invertible matrix.
- `contMDiff_of_contDiffOn`: a function on `GL_N(F)` that agrees with a function `C^∞` on the
  invertible matrices is smooth.

### The right derivative in matrix coordinates

- `differentiableAt_unitsExtension_mul_left`: for smooth `f`, the function
  `y ↦ unitsExtension f (g y)` is differentiable at `y = 1`.
- `rightDerivative_eq_fderiv_mul_left`: for smooth `f`,
  `rightDerivative (matrixModel F N) X f g` is the Fréchet derivative of
  `y ↦ unitsExtension f (g y)` at `1`, applied to `X`.
- `rightDerivative_eq_fderiv`: for smooth `f`,
  `rightDerivative (matrixModel F N) X f g = D(unitsExtension f)(g) (g X)`.
- `contMDiff_rightDerivative`: the right derivative of a smooth function is smooth.
- `rightDerivative_mul_left_of_eq`: if `f` is smooth and `f(a g) = c f(g)` for all `g`, then
  `(R(X) f)(a g) = c (R(X) f)(g)` for all `g`.
- `rightTranslation_rightDerivative`: for smooth `f` and every `k ∈ GL_N(F)`,
  `R(k) (R(X) f) = R(k X k⁻¹) (R(k) f)`. Here `R(k) = Whittaker.rightTranslation ℂ _ k` and
  `R(X) = rightDerivative (matrixModel F N) X`.

### Linearity of the right derivative

- `rightDerivative_add`, `rightDerivative_smul`: for smooth functions, `R(X)` is additive and
  complex-homogeneous.
- `rightDerivative_sum_smul`: `R(∑ r_i Y_i) f = ∑ r_i R(Y_i) f` for real coefficients `r_i`. This
  holds for every `f`, because the manifold derivative is a real-linear map.
- `rightDerivativeLinearMap V hV X` (definition): for a complex subspace `V` of functions on
  `GL_N(F)` all of whose elements are smooth (`hV`), this is the complex-linear map
  `V → (GL_N(F) → ℂ)`, `f ↦ R(X) f`.

### `K`-finiteness for general subspaces and subgroups

In this subsection `V` is a complex subspace of functions on `GL_N(F)` and `K` is any subgroup of
`GL_N(F)`. `V` is assumed stable under right translation by elements of `K`. The space
`kFiniteFunctions V K` is the Library's `V ⊓ kFiniteVectors (Whittaker.rightTranslation ℂ _) K`.

- `rightTranslation_mem_kFiniteFunctions`: if `f ∈ kFiniteFunctions V K` and `k ∈ K`, then
  `R(k) f ∈ kFiniteFunctions V K`. The translates of `R(k) f` are among the translates of `f`.
- `rightDerivative_mem_kFiniteVectors`: if every element of `V` is smooth and
  `f ∈ kFiniteFunctions V K`, then `R(X) f` is `K`-finite for every `X ∈ M_N(F)`. The proof is the
  basis argument in the proof route above.

These two results have no hypothesis on `K` (such as compactness) and no hypothesis on `V` beyond
the ones stated. They can therefore be applied to other spaces of smooth functions, such as
`realStandardModule`, once those spaces are shown to be stable under right translation by `K`.

### Principal series

For a family of characters `χ : ℕ → Fˣ → ℂ`:

- `rightTranslation_mem_principalSeries`: `principalSeries F N χ` is stable under right
  translation by every element of `GL_N(F)`.
- `rightDerivative_mem_principalSeries`: `principalSeries F N χ` is stable under
  `rightDerivative (matrixModel F N) X` for every `X ∈ M_N(F)`.
- `rightTranslation_mem_kFiniteFunctions_principalSeries`: for any subgroup `K`,
  `kFiniteFunctions (principalSeries F N χ) K` is stable under right translation by `K`.
- `rightDerivative_mem_kFiniteFunctions_principalSeries`: for any subgroup `K`,
  `kFiniteFunctions (principalSeries F N χ) K` is stable under every right derivative
  `rightDerivative (matrixModel F N) X`.

### The complex standard modules

- `rightTranslation_mem_kFiniteFunctions_complexStandardModule`: the `U(n)`-finite functions of
  `complexStandardModule n ds` are stable under right translation by `U(n) = unitaryCompact ℂ n`.
- `rightDerivative_mem_kFiniteFunctions_complexStandardModule`: they are stable under every right
  derivative `rightDerivative (matrixModel ℂ n) X`, `X ∈ M_n(ℂ)`.

Both follow from the principal-series results, because `complexStandardModule n ds` is by
definition `principalSeries ℂ n (complexPositionCharacter ds)`.

## Scope

The module proves only these closure properties. It does not prove the Langlands quotient
statements themselves, and it does not construct the `(𝔤, K)`-module structure on the `K`-finite
functions.
