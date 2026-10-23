# Shahidi's intertwining integral on functions

This module implements the integral (0.1) of F. Shahidi, *Fourier transforms
of intertwining operators and Plancherel measures for GL(n)*, American Journal
of Mathematics 106 (1984), 67–111, printed page 72:

\[
A(s,\pi,w_{m,n})f(g)=\int_{U'} f(w_{m,n}u'g)\,du'.
\]

The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The author is Worker 11. It uses the published block Weyl matrix
`blockWeyl m n F` and exchanged radical coordinates
`intertwiningUnipotent m n F` of `Langlands.Representation.Shahidi.Geometry`.
Here `U'` is the exchanged upper radical: an `n` by `m` matrix `a` gives
`u'(a)`, which is `[[I_n,a],[0,I_m]]` transported to total rank `m+n` by
`swapRank`.

The source integrates an element of the induced space `I(s,π)` with values in
the space of `π = π₁ ⊗ π₂`. This unit does not construct that induced
representation. It defines the integral for an arbitrary actual function
`f : GL_(m+n)(F) → V`, with `V` an arbitrary complex vector space carrying an
arbitrary representation `ρ` of an arbitrary topological group `H`. In the
intended application `H = GL_m(F) × GL_n(F)` and `ρ = π₁ ⊗ π₂`. The integral
is the published weak integral of
`Langlands.HarmonicAnalysis.SmoothWeakIntegral`, tested by the smooth dual of
`ρ`. The measure `μ` on the `n` by `m` matrices over `F` is arbitrary. No Haar
property is assumed by the definitions. The specialization to `I(s,π)`, with
the target `I(-s,π')` for `π' = π₂ ⊗ π₁`, is a later unit.

## Two weak-integral lemmas

These two lemmas are internal to this formalization. They are placed in the
namespace `Langlands.HarmonicAnalysis.SmoothWeakIntegral` because they concern
only the weak integral.

`HasIntegral.act` assumes a topological group. If `v` is the weak integral of
`f`, then `ρ(h) v` is the weak integral of `x ↦ ρ(h)(f x)`. For a smooth
functional `ℓ`, the test `ℓ ∘ ρ(h)` is the value of the published
`smoothContragredient ρ h⁻¹ ℓ`. So it is again a smooth test.

`HasIntegral.comp_measurableEquiv` is a change of variables. Let
`e : X ≃ᵐ X` be a measurable equivalence with `μ.map e = c • μ` for some
`c : ℝ≥0`. Then `f ∘ e` has weak integral `c • v`. For each test this is
Mathlib's `integrable_map_equiv` and `integral_map_equiv`, together with
scaling of the measure by `c`.

## The integrand

All other declarations are in `Langlands.Shahidi`. `intertwiningIntegrand m n g`
is the complex-linear map sending `f` to

\[
a\longmapsto f(w_{m,n}\,u'(a)\,g)
\]

on `n` by `m` matrices `a`. It needs only a field `F`. Three algebraic
identities are proved:

- `intertwiningIntegrand_rightTranslate`: the integrand at `g` of
  `x ↦ f(x h)` is the integrand of `f` at `g h`.
- `intertwiningIntegrand_unipotent_mul`: the integrand at `u'(b) g` is
  `a ↦` (integrand at `g`)`(a + b)`. This uses `u'(a) u'(b) = u'(a + b)`.
- `upper_mul_blockSum`: for `h₂ ∈ GL_n(F)` and `h₁ ∈ GL_m(F)`,
  `u(a) diag(h₂,h₁) = diag(h₂,h₁) u(h₂⁻¹ a h₁)`, with `u = upper n m F`.
  This is block multiplication.

## Relation and domain

For a measurable structure on `F`, `HasIntertwiningIntegral m n ρ μ f A` means:
for every `g`, the vector `A g` is the weak integral of
`intertwiningIntegrand m n g f` against `μ`. So for every smooth functional
`ℓ` of `ρ`, the scalar function `a ↦ ℓ(f(w u'(a) g))` is Bochner integrable,
and its integral is `ℓ(A g)`. This is the meaning of the integral (0.1) at
every point. It is not a hypothesis that the integral converges for any
particular `f`.

`intertwiningDomain m n ρ μ` is the submodule of functions whose integrand at
every point lies in the published `integrableSubmodule ρ μ`.
`mem_intertwiningDomain` proves that membership means that some `A` satisfies
the relation. `hasIntertwiningIntegral_zero`, `HasIntertwiningIntegral.add` and
`HasIntertwiningIntegral.smul` give linearity of the relation.

## The operator

Assume `H` is a topological group, `ρ` is smooth, and every open subgroup of
`H` contains a compact open subgroup (`hcofinal`). These are the published
hypotheses of `HasIntegral.unique`. Then `HasIntertwiningIntegral.unique`
proves that `A` is determined by `f`.

`intertwiningOperator m n ρ μ hcofinal hρ` is defined only on
`intertwiningDomain m n ρ μ`. Its value at `g` is the published
`integralLinear` of the integrand at `g`. It is complex linear, and there is
no default value outside the domain.
`hasIntertwiningIntegral_intertwiningOperator` proves that its value satisfies
the relation. `intertwiningOperator_eq` proves that it equals any `A` satisfying
the relation. `intertwiningOperator_eval` proves that every smooth functional
of its value at `g` is the scalar integral
`∫ ℓ(f(w u'(a) g)) dμ(a)`.

## Translation and covariance

The following results hold for the relation. Under the uniqueness hypotheses
above they also hold for the operator.

- Right translation. `HasIntertwiningIntegral.rightTranslate` and
  `rightTranslate_mem_intertwiningDomain` show that the domain is stable
  under `f ↦ f(· h)`, and the integral of the translate is the translate of
  the integral. `intertwiningOperator_rightTranslate` is the operator form.
  This is the function-level part of the intertwining property.
- Left invariance under `U'`. `HasIntertwiningIntegral.unipotent_mul` assumes
  `MeasurableAdd F` and that `μ` is invariant under left translation. Then the
  integrand at `u'(b) g` has weak integral `A g`. The proof builds the
  measurable equivalence `a ↦ a + b` on matrices and uses commutativity of
  matrix addition to apply left invariance. `intertwiningOperator_unipotent_mul`
  is the operator form: `A f(u'(b) g) = A f(g)`.
- Levi covariance. `HasIntertwiningIntegral.levi` takes `h₁ ∈ GL_m(F)`,
  `h₂ ∈ GL_n(F)`, `h ∈ H` and `z ∈ ℂ` such that
  `f(diag(h₁,h₂) x) = z ρ(h)(f(x))` for all `x`. It also takes a measurable
  equivalence `e` with `e(a) = h₂⁻¹ a h₁` and `μ.map e = c • μ`. Then the
  integrand at `diag'(h₂,h₁) x` has weak integral `(z c) ρ(h)(A x)`, where
  `diag'(h₂,h₁)` is `blockSum (h₂, h₁)` transported by `swapRank`.
  `intertwiningOperator_levi` is the operator form. The proof uses the matrix
  identity

  \[
  w_{m,n}\,u'(a)\,\mathrm{diag}'(h_2,h_1)
    =\mathrm{diag}(h_1,h_2)\,w_{m,n}\,u'(h_2^{-1}ah_1).
  \]

  It follows from `upper_mul_blockSum` and the published
  `blockWeyl_conjugate_blockSum`. The source's transformation law on page 72
  has this form: `ρ(h) = π₁(h₁) ⊗ π₂(h₂)`, and `z` is the product of the
  `|det|` powers. The scaling constant `c` is a hypothesis here. Over a
  p-adic field with an additive Haar measure, the Library's
  `PadicRectangularHaarScalingStatement` (proved as
  `padicRectangularHaarScalingStatement`), applied with `A = h₂⁻¹` and
  `B = h₁⁻¹`, gives `c = |det h₂|^m / |det h₁|^n` for the normalized
  determinant norm.

## What is not claimed

This unit does not claim the following:

- that the integral converges for `f ∈ I(s,π)` when `Re s` is large;
- that `A(s,π,w_(m,n))` has a rational continuation in `q^(-s)`;
- that the operator maps `I(s,π)` into `I(-s,π')`;
- any Haar normalization of `du'`.

The source cites these properties to [15, 19, 22] on page 72. They are
obligations for the later specialization to induced representations.
The relation and operator here are the actual integral on its domain. They do
not depend on any of these properties.
