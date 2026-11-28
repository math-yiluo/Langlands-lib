# Restriction of functions with root-hyperplane poles to a subspace

Module `Langlands.Analysis.Meromorphic.RootHyperplaneRestriction`.

## Purpose

Let `X` be a finite-dimensional complex vector space and `f : X → ℂ` meromorphic in linear
coordinates with domain of holomorphy `D` (`IsMeromorphicInCoordinatesOn f D`), with poles along
the hyperplanes of linear forms `L β`, `β ∈ R` (`HasRootHyperplanePoles L R f D`, module
`Langlands.Analysis.Meromorphic.RootHyperplanePoles`). For a complex linear map `τ : V → X` the
composite `f ∘ τ` need not be meromorphic: the domain `D` may contain no point of the image of
`τ`, and off `D` the values of `f` are not controlled. When none of the forms `L β ∘ τ`, `β ∈ R`,
vanishes, the singularities of `f` meet the image of `τ` in a locally finite union of proper
hyperplanes, and after replacing `f` off `D` by its regularization the composite with `τ` is
meromorphic with poles along the hyperplanes of the forms `L β ∘ τ`. This is the step that passes
from a meromorphic function of the parameter of a parabolic `P'` to its restriction to the
parameters `λ|` of a larger parabolic `P ⊇ P'` (Bernstein–Lapid, *On the meromorphic continuation
of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), Theorem 2.3 (6) and §8.6, where the
singularities are along root hyperplanes).

## Regularization on a normed space

Let `E` be a complex normed space, `F : E → ℂ` and `U ⊆ E`.

- `IsClearingData F U W q h`: `W` is open, `q` and `h` are complex differentiable on `W`, and
  `q s * F s = h s` for `s ∈ W ∩ U`.
- `regularDomain F U`: the union of `U` with all points `s` for which some clearing data
  `(W, q, h)` have `s ∈ W` and `q s ≠ 0`.
- `regularization F U s`: `F s` if `s ∈ U`; otherwise `h s / q s` for clearing data `(W, q, h)`
  with `s ∈ W` and `q s ≠ 0`, chosen with `Classical.choose`; `0` if there are none.

For `U` open and dense and `F` complex differentiable on `U`:

- `regularization_of_mem`: the regularization is `F` on `U` (no hypotheses on `U`).
- `IsClearingData.div_eq` (uses only density of `U`): two clearing data `(W, q, h)`,
  `(W', q', h')` give `h s / q s = h' s / q' s` wherever `s ∈ W ∩ W'` and `q s ≠ 0 ≠ q' s`. Both
  quotients are continuous on the open set where both are defined and equal `F` on its
  intersection with `U`, which is dense in it (`EqOn.of_subset_closure`).
- `regularization_eq_div`: at a point `s ∈ W` with `q s ≠ 0` the regularization is `h s / q s`,
  for any clearing data, by the previous item.
- `isOpen_regularDomain`: the regular domain is open (uses only openness of `U`).
- `differentiableOn_regularization`: the regularization is complex differentiable on the regular
  domain: near a point of `U` it agrees with `F`, and near a point `s ∈ W` with `q s ≠ 0` it agrees
  with `h / q` on the open set `W ∩ {q ≠ 0}`.
- `IsClearingData.mul_regularization`: clearing data clear the regularization on all of
  `W ∩ regularDomain F U`: both `q · regularization` and `h` are continuous there and agree on the
  dense subset `W ∩ U`.

## Nonvanishing of products of affine forms

On `ℂⁿ`:

- `differentiable_linearMap_sub`: `t ↦ ψ (t - t₀)` is complex differentiable for a linear form `ψ`.
- `exists_mem_ball_linearMap_ne_zero`: if `ψ ≠ 0`, every ball around `t₀` contains `t` with
  `ψ (t - t₀) ≠ 0` (take `t = t₀ + c • v` with `ψ v ≠ 0` and `c > 0` small).
- `exists_mem_ball_prod_ne_zero`: the same for a finite product `∏ β ∈ S, φ β (t - t₀)` of affine
  forms with nonzero linear parts, by induction on `S` with the identity theorem
  `exists_mul_ne_zero_of_isOpen_subset` (module `Langlands.Analysis.Meromorphic.IdentityTheorem`)
  on the ball.

## The restriction theorem

`exists_comp_linearMap_of_hasRootHyperplanePoles`: let `V` be finite-dimensional, `L : ι → X →ₗ[ℂ] ℂ`,
`R : Set ι`, `f : X → ℂ` with `IsMeromorphicInCoordinatesOn f D` and
`HasRootHyperplanePoles L R f D`, and `τ : V →ₗ[ℂ] X` with `L β ∘ₗ τ ≠ 0` for every `β ∈ R`. Then
there are `f' : V → ℂ` and `D' ⊆ V` with

1. `IsMeromorphicInCoordinatesOn f' D'`;
2. `HasRootHyperplanePoles (fun β => L β ∘ₗ τ) R f' D'`;
3. `f' v = f (τ v)` for every `v` with `τ v ∈ D`.

Proof. Fix the coordinates `e₀ : ℂᴺ ≃ X` of a basis (`Module.finBasis`). In these coordinates
`F = f ∘ e₀` is complex differentiable on the open dense set `U = e₀⁻¹ D`, and the pole data of
`f` at a point `s₀` (an open `W ∋ s₀`, a finite `S ⊆ R`, an exponent `m` and `h`) are clearing data
for `F` on `U` with `q s = (∏ β ∈ S, L β (e₀ s - e₀ s₀)) ^ m`. Let `freg = regularization F U ∘ e₀⁻¹`
and `Dreg = e₀ (regularDomain F U)`. Then `freg = f` on `D`, `freg` is complex differentiable on
`Dreg` in every linear coordinate system, and `D ⊆ Dreg` is dense in coordinates, so
`HasRootHyperplanePoles.of_eqOn_dense` transfers the pole data of `f` to
`HasRootHyperplanePoles L R freg Dreg`. Put `f' = freg ∘ τ` and `D' = τ⁻¹ Dreg`;
`HasRootHyperplanePoles.comp_linearMap` gives (2), and (3) holds since `freg = f` on `D`.

For (1) it suffices to treat the coordinates `e' : ℂⁿ ≃ V` of a basis
(`isMeromorphicInCoordinatesOn_of_coordinates`). Let `A = e₀⁻¹ ∘ τ ∘ e'`, a continuous linear map
`ℂⁿ → ℂᴺ`, so that `f' ∘ e' = regularization F U ∘ A` and `e'⁻¹ D' = A⁻¹ (regularDomain F U)`,
which is open. At `t₀ ∈ ℂⁿ` take the pole data of `f` at `A t₀` and a ball `B` around `t₀` with
`A B ⊆ W`. On `B` the denominator pulls back to `g t = (∏ β ∈ S, φ β (t - t₀)) ^ m` with
`φ β = L β ∘ τ ∘ e' ≠ 0`, which is not identically zero on `B` (`exists_mem_ball_prod_ne_zero`).
Hence the points of `B` where `g ≠ 0` are dense in `B`
(`subset_closure_inter_ne_zero`), and they lie in `A⁻¹ (regularDomain F U)`; so the domain is dense.
The regularization is complex differentiable on the regular domain, and on the connected ball `B`
the function `g` times `f' ∘ e'` equals `h ∘ A` on the domain
(`IsClearingData.mul_regularization`). These are the conditions of `isMeromorphicOn_iff`.
