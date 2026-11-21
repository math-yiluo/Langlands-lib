# Reduction of adelic local finiteness to weighted Hilbert models

`Langlands.Global.uniformGrowthLocalFiniteness_of_hilbertModel` proves the
conditional implication from `UniformGrowthLocalFinitenessHilbertModelStatement`
to the unchanged `UniformGrowthLocalFinitenessStatement.{u}`. The Hilbert-model
proposition is a remaining obligation, **not** an established theorem. The
reduction retains all the original number-field, group, parameter and compact
open level data and does not modify the target or its imports. The model's
Hilbert domain and codomain have independent universes.

## The input model

`LocalFinitenessData.HilbertModel` is data for a base point `s₀` and an index `i`
with nonzero eigenvalue `cᵢ(s₀)`. It asks for:

- A common parameter neighbourhood and growth exponent `R₀`, and families
  `lhs(s), rhs(s) : B →L[ℂ] C` between Hilbert spaces. Both are weakly
  holomorphic. The left family at `s₀` is a topological embedding and the
  right family at `s₀` is compact.
- For each of the finitely many test kernels in equation `i`, a bounded
  realization `Tₖ : B →L[ℂ] B` and a smooth realization
  `Kₖ : B →L[ℂ] 𝔉^{R₀}_L`. Write `T(s)` and `K(s)` for their combinations
  with scalars `bᵢₖ(s)/cᵢ(s)`. The model must verify that `K(s₀)x = 0`
  implies `T(s₀)x = 0`.
- `lift_solution`: for every actual solution at any `R ≥ R₀`, there is a
  Hilbert lift `x` satisfying `lhs(s)x = rhs(s)x` and `T(s)x = x`. The
  function of `K(s)x` must agree pointwise with the normalized combination
  of the original convolutions applied to the solution. Agreement is required
  for the **sum**, not each kernel separately: left averaging the individual
  kernels at `L` can change individual convolutions. Applying the right-level
  averaging projection to their combined reproducing equation leaves the
  right-`L`-invariant solution unchanged.

The intended model takes `lhs` from difference polynomials in cusp and
central coordinates and restriction to boundary strips, and `rhs` from the
smoothed boundary restrictions. The model proposition calls for existence
with a usable index at each base point; it does not presuppose a Fréchet
finite-type family.

## Implemented proof

`LocalFinitenessData.finiteType_on_of_hilbertModel` intersects the model
neighbourhood with the open set where `cᵢ` is nonzero. Testing with the scalar
identity gives manifold differentiability of the given coefficients, so the
normalized coefficients are holomorphic there. The finite sum defining `T`
is weakly holomorphic, and so is `A = lhs − rhs`.

At the base point, the topological embedding `lhs(s₀)` has closed range by
its antilipschitz bound and completeness of `B`. The orthogonal complement
of its range in `C` gives a continuous left inverse `D`. Thus
`D A(s₀) − 1 = −D rhs(s₀)` is compact. Evaluation at adelic points separates
vectors in `𝔉^{R₀}_L` by injectivity of `toFun`. Apply
`reproducingFredholmFiniteType` with these evaluations to obtain a
finite-dimensional family in `𝔉^{R₀}_L` covering the smoothed joint kernels.

For an actual solution `f`, its lift satisfies the Hilbert equations. The
pointwise agreement in the model, followed by the actual Harish-Chandra
equation for `i`, identifies the function of `K(s)x` with the function of `f`.
`weakenCLM` is the injective continuous inclusion into `𝔉^R_L` for `R ≥ R₀`;
composing the witness with it preserves weak holomorphy and injectivity and
covers `f`. The same neighbourhood works for every such `R`.

## Provenance and open obligations

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, Theorem 7.2 (p.212)
and §§7.3–7.7 (pp.212–221), especially (7.3), (7.5), (7.6), and the use of
Corollary 3.4 in §7.6. This is a derived interface for the proof, not a separate
assertion in the source. The formal argument uses the exact-fiber reproducing
transfer rather than the paper's approximate-identity adjustment.

The actual weighted spaces on adelic Siegel domains, constant-term projections,
strict norm estimate, compactness of boundary convolution, level-preserving
smoothing with a common growth bound, and membership and compatibility of
all actual solutions in that model are not proved by this module.
