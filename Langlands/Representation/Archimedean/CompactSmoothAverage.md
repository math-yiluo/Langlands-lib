# Genuine derivatives of compact smooth orbit averages

Module `Langlands.Representation.Archimedean.CompactSmoothAverage`.

## Setting

`G` is a real Lie group (`LieGroup 𝓘(ℝ, 𝔤) ∞ G`) modelled on a normed
real space `𝔤` through the boundaryless model `𝓘(ℝ, 𝔤)`. `N` is a smooth
real manifold (`IsManifold 𝓘(ℝ, H) ∞ N`) modelled on a normed real space
`H`, which may be infinite-dimensional. `E` is a complex normed space and
`π : G →* (E →L[ℂ] E)` is a homomorphism into bounded operators. No
continuity of the action map is assumed. A family `v : N → E` is
assumed to have a jointly smooth orbit family: `(g, n) ↦ π g (v n)` is
`ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞` on `G × N`.

The derivatives are the published genuine ones. `lieDerivative 𝓘(ℝ, 𝔤) π X v`
is the actual manifold derivative `mfderiv` at `1` of the orbit map
`g ↦ π g v`, evaluated at `X`. `iteratedLieDerivative` of the word
`[X₁, …, Xₖ]` is `dπ(X₁)(dπ(X₂)(⋯ dπ(Xₖ) v))`, and the empty word gives `v`.
`DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π` is the published copy of the smooth
vectors whose topology is induced by `derivativeCoordinates`. This map sends
a vector to the family of all its genuine word derivatives in the product
space `List 𝔤 → E`.

## Joint smoothness of all derivative families

`isSmoothVector_family` restricts the orbit family to `G × {n}`, so every
`v n` is a genuine smooth vector. `continuous_family` restricts it to
`{1} × N` and uses `π 1 = id`, so `v` is continuous.

`contMDiff_orbit_lieDerivative` shows that for each `X : 𝔤` the family
`n ↦ dπ(X)(v n)` again has a jointly smooth orbit family.

- *Actual differentiated orbit family.* The proof uses the jointly smooth map
  `((g, n), h) ↦ π (g * h) (v n)` on `(G × N) × G`. It is the hypothesis
  composed with `((g, n), h) ↦ (g * h, n)`. Mathlib's
  `ContMDiffAt.mfderiv_apply` differentiates this map in the last variable,
  at the constant point `h = 1` and in the constant direction `X`. The
  result is smooth in `(g, n)` when written in tangent coordinates.
- *Tangent coordinate identification.* The base point is constantly `1`, so
  the source coordinate change compares the chart at `1` with itself. This is
  the identity by `tangentCoordChange_self`. The target is the vector space
  `E`, whose model-space coordinate change is the identity by
  `tangentBundleCore_coordChange_model_space`. So `inTangentCoordinates`
  equals the actual `mfderiv` of `h ↦ π (g * h) (v n)` at `1`.
- *Identification with the genuine Lie derivative.* The published
  `apply_lieDerivative` rewrites this derivative, evaluated at `X`, as
  `π g (dπ(X)(v n))`. It applies because `v n` is a smooth vector.

`contMDiff_orbit_iteratedLieDerivative` proceeds by *induction on genuine
derivative words*. The empty word is the hypothesis. For `X :: Xs`, the
previous step is applied to the family `n ↦ iteratedLieDerivative Xs (v n)`,
whose orbit family is jointly smooth by the induction hypothesis.
`continuous_iteratedLieDerivative_family` then makes each derivative family
`n ↦ iteratedLieDerivative Xs (v n)` continuous.

`continuous_derivativeFamily` proves that `n ↦ v n` is continuous into
`DerivativeSmoothVectors`. The topology there is induced by
`derivativeCoordinates`, so `continuous_induced_rng` reduces this to
continuity into the product. `continuous_pi` then reduces it to continuity of
each word coordinate `n ↦ iteratedLieDerivative Xs (v n)`.

## Compact integration

From here on `𝔤` is finite-dimensional and `E` is complete. `X` is a compact
topological space with its Borel measurable structure (`BorelSpace X`) and a
finite measure `μ`. The weight is `a : C(X, ℂ)` and the restriction map is
`j : C(X, N)`, which is only required to be continuous.

- `integrable_family`: `x ↦ a x • v (j x)` is continuous on a compact space,
  hence Bochner integrable.
- `apply_integral`: each bounded operator `π g` commutes with the Bochner
  integral (`ContinuousLinearMap.integral_comp_comm`).
- `isSmoothVector_integral`: the orbit map of `∫ x, a x • v (j x) ∂μ` is
  `g ↦ ∫ x, a x • π g (v (j x)) ∂μ`. This map is smooth by
  `Langlands.Analysis.CompactManifoldVectorIntegral.contMDiff_weightedIntegral`
  with `M = G` and `h (g, n) = π g (v n)`.
- `lieDerivative_integral`: `dπ(Y)` of the integral equals
  `∫ x, a x • dπ(Y)(v (j x)) ∂μ`. This is
  `Langlands.Analysis.CompactManifoldVectorIntegral.mfderiv_weightedIntegral_apply`
  at `p = 1`, evaluated at `Y`.
- `iteratedLieDerivative_integral` is the *all-word identity*. Induction on
  the word applies `lieDerivative_integral` to the derivative family
  `n ↦ iteratedLieDerivative Xs (v n)`. This is allowed because that family's
  orbit family is jointly smooth by `contMDiff_orbit_iteratedLieDerivative`.

## Continuous averaging into the full derivative topology

`weightAverageLM` sends a weight `b` to the element of
`DerivativeSmoothVectors` whose underlying vector is the actual Bochner
integral `∫ x, b x • v (j x) ∂μ`. Complex linearity follows from
`integral_add` and `integral_smul`. `derivativeCoordinates_weightAverageLM`
identifies the `Xs` coordinate with
`∫ x, b x • iteratedLieDerivative Xs (v (j x)) ∂μ`.

`continuous_weightAverageLM` gives continuity with respect to the uniform
norm on `C(X, ℂ)`.

- *Uniform norm estimate for each derivative coordinate.* Fix a word `Xs` and
  let `F : C(X, E)` be `x ↦ iteratedLieDerivative Xs (v (j x))`. The map
  `L b = ∫ x, b x • F x ∂μ` is complex linear and satisfies
  `‖L b‖ ≤ (‖F‖ * μ.real Set.univ) * ‖b‖`. Here `‖b‖` and `‖F‖` are the
  uniform (sup) norms on the compact space `X`. The bound is
  `norm_integral_le_of_norm_le_const` applied to the pointwise bound
  `‖b x • F x‖ ≤ ‖b‖ * ‖F‖`. `LinearMap.mkContinuous` makes each coordinate
  continuous.
- *Induced-topology continuity.* The derivative topology is induced into the
  product over all words, so `continuous_induced_rng` and `continuous_pi`
  turn the continuity of every coordinate into continuity of
  `weightAverageLM`.

`weightAverageCLM` bundles the map as a `C(X, ℂ) →L[ℂ] DerivativeSmoothVectors`.
`toSmooth_weightAverageCLM` records its underlying integral.
`weightAverage_mem_closure_image` is the consequence of density. If
`S ⊆ C(X, ℂ)` is dense, every average lies in the closure, taken in the
derivative topology, of the averages with weights in `S`.

## Specialization to translates of a smooth vector

`contMDiff_orbit_family` shows that for a genuine smooth vector `w` the family
`v g = π g w`, indexed by `N = G` with model `H = 𝔤`, has a jointly smooth
orbit family. Indeed `π g (π h w) = π (g * h) w` is the smooth orbit map of
`w` composed with group multiplication. For `r : C(X, G)` the preceding
results therefore apply to `∫ x, a x • π (r x) w ∂μ`:

- `isSmoothVector_orbitIntegral`: smoothness;
- `iteratedLieDerivative_orbitIntegral`: the all-word identity;
- `orbitAverageCLM`: the continuous complex linear map into
  `DerivativeSmoothVectors`, with `toSmooth_orbitAverageCLM` and
  `derivativeCoordinates_orbitAverageCLM`;
- `orbitAverage_mem_closure_image`: the closure-image consequence.

## The statement

`Langlands.Archimedean.CompactSmoothAverageStatement` quantifies over six
independent universes: those of the Lie group model `𝔤`, the Lie group `G`,
the family model `H`, the family manifold `N`, the Banach space `E` and the
compact integration space `X`. For every jointly smooth orbit family `v` it
asserts four things:

1. the orbit family of every genuine word derivative of `v` is jointly smooth;
2. `v` is continuous into `DerivativeSmoothVectors`;
3. every weighted integral `∫ x, a x • v (j x) ∂μ` is a genuine smooth vector;
4. there is a continuous complex linear `A : C(X, ℂ) →L[ℂ] DerivativeSmoothVectors`
   whose underlying vector at `a` is that actual integral. For every word
   `Xs`, its derivative coordinate is
   `∫ x, a x • iteratedLieDerivative Xs (v (j x)) ∂μ`.

`compactSmoothAverage` proves the statement with the constructions above,
taking `A = weightAverageCLM`. The translate specialization and the
closure-image consequence are supplied as the theorems named above rather
than as conjuncts of the statement.

## Provenance and scope

This is an internal development with no external literature source. It
consists of calculus deductions from the published genuine smooth-vector
definitions (`Langlands.Representation.Archimedean.SmoothVectors`,
`SmoothDerivative`, `SmoothDerivativeTopology`), Mathlib's manifold calculus
and Bochner integration, and the separately published compact
vector-manifold integration result of Task 7699 in
`Langlands.Analysis.CompactManifoldVectorIntegral`. That result is imported
by Lean name and is not duplicated here. The module is infrastructure for
approximation in the genuine smooth-vector topology. It asserts no
compact-finite density, no cuspidal globalization or comparison with an
actual cuspidal realization, no extension of functionals and no
multiplicity-one theorem.
