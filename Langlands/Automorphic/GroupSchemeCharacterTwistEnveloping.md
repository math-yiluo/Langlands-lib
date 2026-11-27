# Multiplication by a smooth character and the enveloping action on `G(F_∞)`

Module `Langlands.Automorphic.GroupSchemeCharacterTwistEnveloping`.

## Calculus on a Lie group

For a Lie group `G` modelled on a real normed space, `groupDirectionalValue I X f g` is the
derivative of `h ↦ f(g h)` at the identity in the direction `X` of the Lie algebra (the right
orbit derivative used by the Library's enveloping actions).

- `Langlands.Geometry.Manifold.groupDirectionalValue_fun_mul` is the Leibniz rule for smooth
  complex functions: `X(f h)(g) = (X f)(g) h(g) + f(g) (X h)(g)`. It is Mathlib's product rule
  `HasMFDerivAt.mul`, applied at the identity to `z ↦ f(g z)` and `z ↦ h(g z)`.
- `Langlands.Geometry.Manifold.groupDirectionalValue_of_map_mul`: if `χ` is smooth and
  `χ(xy) = χ(x)χ(y)`, then `(Xχ)(g) = χ(g) (Xχ)(1)`, since `y ↦ χ(g y)` is the constant multiple
  `χ(g) • χ` and the derivative is complex linear (`groupDirectionalValue_const_smul`).

## On the infinite adelic points

Let `G` be an affine group scheme over a number field `F` and `G(F_∞)` its infinite adelic
points with the smooth structure given by `hsmooth`.

- `mul_mem_infinitePlotSmoothFunctions`: plot-smooth functions on `G(F_∞)` are closed under
  pointwise products. This is checked on every coordinate-smooth family with `contDiff_mul`.
- `plotSmoothMultiplication F G χ hχ` is multiplication by a fixed plot-smooth function `χ`, as
  a complex-linear endomorphism of `InfinitePlotSmoothFunctions F G`
  (`plotSmoothMultiplication_apply`).
- `exists_centerShift_plotSmoothMultiplication`: if `χ` is plot-smooth, `χ(xy) = χ(x)χ(y)` and
  `χ(1) = 1`, there is an algebra endomorphism `θ` of the center
  `AdelicEnvelopingCenter F G hsmooth` of the complex enveloping algebra such that
  `z · (χ u) = χ · (θ(z) · u)` for every central `z` and every plot-smooth `u`, the action being
  `plotSmoothCenterAction F G hsmooth hcalc`.

Proof of the last statement. The Library's enveloping action is the extension to `U(𝔤_ℂ)` of the
complexification `ρ` of the real Lie action `X ↦ D_X` (`realPlotSmoothLieAction`). Let `T` be
multiplication by `χ` and `μ` the complex-linear extension of `X ↦ (Xχ)(1)`. On a generator
`w ⊗ X` the two lemmas above give

`w D_X(χ u) = χ (w D_X u + w (Xχ)(1) u)`,

that is, `ρ(Z) T = T (ρ(Z) + μ(Z))` for every `Z ∈ 𝔤_ℂ`. This extends to all `Z` by additivity.
Moreover `T ≠ 0`, because `T` sends the constant function `1` to `χ` and `χ(1) = 1`.
`Langlands.Algebra.EnvelopingCharacterShift.exists_centerShift_intertwining` then provides `θ`.
In particular `μ` vanishes on brackets, so the derivative of a smooth character is a Lie algebra
character; no separate computation is needed.

## Provenance

Internal. The relation `y · (χ u) = χ · (shift_{dχ}(y) · u)` is derived from the Leibniz rule
(Mathlib's `HasMFDerivAt.mul`) and the universal property of the enveloping algebra, through
`Langlands.Algebra.EnvelopingCharacterShift`. It is used with a finite transfer of enveloping
centers to a Levi subgroup, as in Mœglin–Waldspurger, *Spectral decomposition and Eisenstein
series* (1995), I.2.17, printed pp. 37–38. For the character `m ↦ m_P(m)^λ` of the Levi, `θ`
composed with the transfer pulls a cofinite ideal of the Levi center back to one that kills the
twist `φ_λ`. This gives the `𝔷`-finiteness in the assertion "`φ_λ ∈ 𝒜_P`" of Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §2.2,
p. 191 (`Langlands.Global.parameterTwistCenterFiniteReduction`).
