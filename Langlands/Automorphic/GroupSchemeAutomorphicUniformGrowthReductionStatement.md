# Uniform growth of adelic automorphic forms from an elliptic estimate and a Casimir element

Author: Worker 723.

`AdelicAutomorphicUniformGrowthReductionStatement` (universe `u`) is the implication

`LieGroupEllipticInteriorEstimateStatement.{u, u} → AdelicAdaptedCasimirStatement.{u} →
AdelicAutomorphicUniformGrowthStatement.{u}`.

- `Langlands.Geometry.Manifold.LieGroupEllipticInteriorEstimateStatement` (module
  `Langlands.Geometry.Manifold.LieGroupEllipticEstimateStatement`) is the interior estimate for
  elliptic left-invariant word operators on Lie groups. It is used at universes `u, u`, which
  are the universes of `smoothModel F d` and `InfiniteAdelicGroupPoints F G` for `F : Type u`.
- `Langlands.Automorphic.GroupSchemeFunctions.AdelicAdaptedCasimirStatement` (module
  `GroupSchemeAdaptedCasimirStatement`) is the adapted Casimir element on the actual infinite
  adelic points.
- `Langlands.Automorphic.GroupSchemeFunctions.AdelicAutomorphicUniformGrowthStatement` (module
  `GroupSchemeAutomorphicUniformGrowthStatement`) is the published, unchanged target: every
  actual adelic automorphic form of a connected reductive group has uniformly moderate growth.

The statement is only an implication. It proves none of the three propositions.

## Intended proof

The intended proof follows Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series*
(1995), I.2.17 (printed pp. 37–39), and Harish-Chandra, *Two theorems on semi-simple Lie
groups* (1966), Lemma 33. The convolution step of MW I.2.5 is replaced by the elliptic
estimate.

1. Let `f` be a form. Let `W` be the span of its `Kinf`-translates, which is finite-dimensional.
   The space `Z · W`, obtained by applying the centre `Z` of the enveloping algebra to `W`, is
   finite-dimensional. Indeed, translation by `k ∈ Kinf` intertwines the action of `z ∈ Z` with
   that of its adjoint conjugate, which is again central, and `f` is centre-finite.
2. The derivative along a vector tangent to a smooth curve in `Kinf` maps `W` into itself, so
   `Z · W` is stable under `∑ i, X i² = ω + 2 ∑_{j ∈ J} X j²`. Hence a monic polynomial
   `p(∑ i, X i²)` annihilates `f`. Its top part `(∑ i, X i²)^m` has symbol `(∑ i, ξ(X i)²)^m`,
   which is nonzero for `ξ ≠ 0` because the `X i` span.
3. Apply the interior estimate to the left-translated slices `x ↦ f(g x)`. All of them satisfy
   the same equation. This bounds every enveloping derivative at `g` by a constant times the
   supremum of `|f|` on `g V`, where `V` is a fixed compact set.
4. The moderate-growth bound `|f(h)| ≤ C ‖h‖^d` of `f` and the submultiplicativity of the height
   (`adelicHeight_mul_le`) then give one exponent `d` for all derivatives.
