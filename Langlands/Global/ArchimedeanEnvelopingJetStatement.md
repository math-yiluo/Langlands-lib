# From genuine enveloping vanishing to ambient matrix zero jets

Authors: Worker 94 (original draft) and Worker 878. Namespace:
`Langlands.Global.ArchimedeanGL`.

`Langlands.Global.ArchimedeanGL.EnvelopingZeroJetStatement K n` is a
proposition for an arbitrary number field `K : Type u` and every natural
rank `n`, including `n = 0`. The module imports only the published
`Langlands.Global.ArchimedeanEnvelopingAction`, and uses its actual
carriers unchanged: the smooth complex-valued functions
`SmoothFunctions K n`, the enveloping algebra `EnvelopingAlgebra K n` of
the complexified real matrix Lie algebra, the differential action
`envelopingAction K n`, the coordinate homeomorphism
`archimedeanGLCoordinates K n` from the completion-based group
`GL_n(InfiniteAdeleRing K)` to the mixed-coordinate group
`ArchimedeanGL K n`, and the ambient expression
`coordinateExtension K n f : ArchimedeanMatrix K n → ℂ`. It does not
depend on any unpublished Casimir, Cartan-symbol, analytic-jet or
polynomial-annihilation draft.

## The proposition and its quantifier order

For every `f : SmoothFunctions K n` and then every basepoint
`x₀ : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)`,
assume

```
∀ a : EnvelopingAlgebra K n, (envelopingAction K n a f).val x₀ = 0.
```

Then, for every `m : ℕ`,

```
iteratedFDeriv ℝ m (coordinateExtension K n f)
  (archimedeanGLCoordinates K n x₀ : ArchimedeanMatrix K n) = 0.
```

The function and the basepoint are fixed first. The single hypothesis
quantifies over all enveloping elements, but only at that one point
`x₀`. The order `m` is quantified only in the conclusion, so the one
hypothesis yields every order. The jet is taken at the unit matrix
`(archimedeanGLCoordinates K n x₀ : ArchimedeanMatrix K n)`, the
mixed-coordinate image of `x₀`.

## The genuine vector-field formula

`envelopingAction K n` is the published universal-enveloping lift of the
complex-linear extension of the actual real directional differential. By
the published `envelopingAction_real_generator_apply`, a real direction
`X : RealLieAlgebra K n`, embedded as
`envelopingGenerator K n (complexify K n X)`, acts on `f` at a point with
mixed-coordinate matrix `g` by

\[
(D_X f)(g) = dF_g(g X),\qquad F = \texttt{coordinateExtension}\ K\ n\ f .
\]

Here `dF_g` is the real Fréchet derivative and `g X` is the matrix
product. As the published `ArchimedeanSmoothDifferential` documents, this
is the left-invariant matrix vector field for the right-translation
convention `R(h)f(g) = f(gh)`. By `envelopingAction_one` the element
`a = 1` acts as the identity, and by `envelopingAction_mul` products act
by composition. In particular the hypothesis contains `f.val x₀ = 0`
(from `a = 1`) and the vanishing at `x₀` of every finite composition
`D_{X₁} ⋯ D_{X_k} f` of these genuine operators. The statement supplies
no frame-comparison certificate, coefficient formula or other auxiliary
hypothesis.

## Conventions and exact scope

- `ArchimedeanMatrix K n` keeps its published structure: square matrices
  with entries in the mixed space of `K`, regarded as a real vector space
  with the `L^∞` operator norm opened by `Matrix.Norms.Operator` (as in
  `ArchimedeanSmoothDifferential`) and its induced topology. Both real
  directions at each complex place are retained. Function values stay
  complex, and all derivatives are over `ℝ`.
- Each order asks for the whole continuous real-multilinear map
  `iteratedFDeriv ℝ m (coordinateExtension K n f)` to be zero at that
  point. This means vanishing on every `m`-tuple of ambient real matrix
  directions, not only on directions of the form `g X`.
- Order `m = 0` is included. By Mathlib's `iteratedFDeriv_zero_apply` and
  the published `coordinateExtension_apply`, it says `f.val x₀ = 0`.
- The coordinate extension enters only at a unit matrix. There
  `coordinateExtension_contDiffAt` gives genuine local `C∞` regularity, so
  the iterated derivatives are actual derivatives. By Mathlib's
  `Filter.EventuallyEq.iteratedFDeriv` they depend only on values near the
  point, where `coordinateExtension_apply` identifies the extension with
  `f`. Its values at non-invertible matrices therefore cannot affect the
  conclusion.
- The rank `n = 0` is included without special treatment.
- No analyticity, vanishing on a neighborhood, finite-dimensional orbit
  or vanishing of ambient jets is assumed.

## Provenance

This is an internal local differential-calculus bridge; it claims no
external literature theorem in these coordinates. Mathematically it
expresses the standard fact that left-invariant vector fields form a
global frame on a Lie group, so that ordinary derivatives at a point are
controlled by enveloping derivatives there; the route below indicates how
the moving frame must be handled in the published coordinates. Worker 94
formulated it as a focused prerequisite of the automorphic
differential-growth task `e0d3fab3-d5c8-47ae-bd65-d85037d6fd80`. That
task's source map, `notes/automorphic/differential-growth-source-map.md`,
describes how vanishing of all jets enters Harish-Chandra's density
argument and lists analytic regularity and jet uniqueness among separate
obligations. The statement is published through task
`3353797b-5844-4dda-a22b-075247445ee8`. Its conclusion has exactly the
form of the jet hypothesis of the published
`AnalyticMatrixJetUniquenessStatement` for the same `f` and `x₀`.
Neither proposition assumes the other.

## Prospective proof route

No proof is included. One route fixes `x₀` and inducts on the order `k`,
for all enveloping elements simultaneously. Write `p` for the
mixed-coordinate unit matrix of `x₀` and `F_a` for the coordinate
extension of `envelopingAction K n a f`. Order zero is the hypothesis
applied to each `a`. For the inductive step, the identity
`dF_a(h)(h X) = F_{X a}(h)` holds near `p`, where `X a` is the product of
the generator of `X` with `a`. Differentiating the left side `k` times at
`p` gives the term `D^{k+1} F_a(p)(p X, v₁, …, v_k)`. Because the frame
`h ↦ h X` varies with `h`, it also gives lower-order terms
`D^k F_a(p)(v_i X, …)`, which vanish by the inductive hypothesis for the
same `a`. The `k`-th derivative of the right side vanishes by the
inductive hypothesis for `X a`. Since `p` is invertible,
`X ↦ p X` is onto the ambient matrix space, so `D^{k+1} F_a(p) = 0`.
First-order frame surjectivity alone does not handle the moving-frame
terms at higher orders.

## What is not stated

This module defines only the proposition. It does not prove analytic
regularity, analytic uniqueness, vanishing outside the basepoint or on
its connected component, Lie-orbit density, reproduction, or the final
automorphic differential-growth theorem. Its proof requires a separate
exact-target task after independent publication of this statement.
