# The uniform-growth Fréchet spaces are Hausdorff locally convex spaces

Module `Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances`
proves the basic topological-vector-space facts about the weighted spaces
`UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L` (written `𝔉`
below) of module `Langlands.Automorphic.GroupSchemeUniformGrowthFrechet`.
The principle of meromorphic continuation
(`Langlands.Analysis.Meromorphic.ContinuationPrincipleStatement`) asks its
target space to be a Hausdorff locally convex topological vector space over
`ℂ`, and the meromorphic continuation of Eisenstein series compares
`𝔉`-valued functions through their values at points of `G(𝔸)`. This module
supplies both.

## Provenance

Internal. The topology on `𝔉` is the one defined in the Library: the
coarsest topology making every weighted derivative
`f ↦ (a f)(·) ‖·‖^{-R}` (one for each element `a` of the complex enveloping
algebra) continuous into the bounded functions `ℓ^∞(G(𝔸))`. The facts below
are routine consequences of that definition. Bernstein–Lapid §7.1
(registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`,
journal pp.210–211) call these spaces Fréchet spaces; this module proves
only the parts used later (no completeness or metrizability).

## Contents

- `weightedDerivative_apply`: the defining formula of the weighted derivative
  `weightedDerivative … a f`. At `x` its value is `(a f)(x)` times
  `(‖x‖^R)⁻¹`, where `‖x‖` is
  `RepresentationGrowth.adelicSourceNorm F G rho x`. The proof is `rfl`.
- `weightedDerivativeLinearMap … a`: the weighted derivative along `a` as a
  `ℂ`-linear map `𝔉 →ₗ[ℂ] ℓ^∞(G(𝔸), ℂ)`. Additivity and homogeneity come
  from the linearity of the enveloping-algebra action.
- `weightedDerivativeCLM … a`: the same map as a continuous linear map. It is
  continuous because the topology of `𝔉` is the infimum of the topologies
  induced by these maps.
- Instances on `𝔉`:
  - `IsTopologicalAddGroup` and `ContinuousSMul ℂ`: an infimum of topologies
    induced by linear maps into topological vector spaces.
  - `LocallyConvexSpace ℝ`: the same infimum, with the maps viewed as
    `ℝ`-linear, into the normed (so locally convex) space `ℓ^∞`.
  - `T2Space`: the weighted derivative along the unit `1` is continuous and
    injective into a Hausdorff space.
- `weightedDerivative_one_apply`: along `1` the weighted derivative is
  `f(x) (‖x‖^R)⁻¹`, with `f(x)` the value
  `UniformGrowthFrechetSpace.toFun … f x` of the underlying function.
- `toFun_injective`: an element of `𝔉` is determined by its underlying
  function on `G(𝔸)`.
- `weightedDerivative_one_injective`: the weighted derivative along `1` is
  injective. The weight `‖x‖^R` is positive because `N > 0`
  (`adelicSourceNorm_pos`).
- `UniformGrowthFrechetSpace.evalCLM … x`: evaluation at `x ∈ G(𝔸)` as a
  continuous linear form `𝔉 →L[ℂ] ℂ`. It is `‖x‖^R` times the evaluation at
  `x` of the weighted derivative along `1`.
- `UniformGrowthFrechetSpace.evalCLM_apply`: `evalCLM … x f` is the value
  of the underlying function of `f` at `x`.

## Lean notes

The local `AddCommGroup` instance on the finite plot-smooth carrier repeats
the one the Library module uses to state its definitions. Without it, the
types of the weighted derivatives would not unify.
