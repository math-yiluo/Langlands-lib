# Families of functions in a finite-dimensional space of functions

Module: `Langlands.Representation.Archimedean.RealInductionStagesFamily`.

## Purpose and provenance

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealAdjacentFiltrationInStagesStatement` (induction in stages of adjacent
filtrations, Task 7068). That proof averages linear maps between spaces of `O(r)`-finite
functions over the compact group `O(r)` and differentiates families of such functions. The
averaged or differentiated family always takes values in one finite-dimensional space of
functions, and this module shows that pointwise integrals and pointwise derivatives of such
families stay in that space and commute with every linear map defined on it.

The key fact is elementary linear algebra: a linear functional on a finite-dimensional space
of functions is a finite linear combination of point evaluations, because the point
evaluations span the dual space. The module makes no literature assertion, so it has no
literature sources.

Throughout, `X` and `Y` are types, `U`, `V` are submodules of `X → ℂ` with `U`
finite-dimensional, and `W` is a submodule of `Y → ℂ`. All declarations are in the namespace
`Langlands.Archimedean.InductionStages`.

## Declarations

### Point evaluations

- `exists_eval_sum U ℓ`: every linear functional `ℓ` on `U` has the form
  `ℓ u = ∑ᵢ cᵢ u(pᵢ)` for finitely many points `pᵢ ∈ X` and coefficients `cᵢ ∈ ℂ`. Proof: the
  Library lemma `exists_sum_of_separating` (module `PrincipalSeriesGKModule`) applied to the
  point evaluations restricted to `U`, which separate the elements of `U`.
- `exists_decomposition U`: there are finitely many functions `bᵢ ∈ U`, points `pᵢₗ ∈ X` and
  coefficients `aᵢₗ ∈ ℂ` such that every `u ∈ U` equals `∑ᵢ (∑ₗ aᵢₗ u(pᵢₗ)) bᵢ`. Proof: take a
  basis `bᵢ` of `U` and write each coordinate functional of the basis by `exists_eval_sum`.

### Integrals

Let `μ` be a measure on a measurable space `K`, and `w : K → X → ℂ` a family with `w k ∈ U`
for all `k` and `k ↦ w k x` integrable for all `x`.

- `integral_mem μ U hw hi`: the function `x ↦ ∫ w k x dμ(k)` lies in `U`. Proof: by
  `exists_decomposition`, `w k x = ∑ᵢ cᵢ(k) bᵢ(x)` with integrable coefficients
  `cᵢ(k) = ∑ₗ aᵢₗ w k (pᵢₗ)`, so the integral is `∑ᵢ (∫ cᵢ dμ) bᵢ ∈ U`.
- `exists_map_eval_sum L U hUV y`: for a linear map `L : V →ₗ[ℂ] W` and `U ≤ V`, the value at
  `y ∈ Y` of `L u` is `∑ᵢ cᵢ u(pᵢ)` for all `u ∈ U`, by `exists_eval_sum` applied to
  `u ↦ (L u)(y)`.
- `integrable_map`: the function `k ↦ (L (w k))(y)` is integrable, being a finite linear
  combination of the integrable functions `k ↦ w k (pᵢ)`.
- `map_integral`: `(L (∫ w k dμ))(y) = ∫ (L (w k))(y) dμ(k)`. Proof: both sides equal
  `∑ᵢ cᵢ ∫ w k (pᵢ) dμ(k)` by `exists_map_eval_sum`.

### Continuity

- `continuous_map L U hUV hw hc y`: if `K` is a topological space and `k ↦ w k x` is
  continuous for every `x`, then `k ↦ (L (w k))(y)` is continuous, again by
  `exists_map_eval_sum`.

### Derivatives

Let `w : ℝ → X → ℂ` be a family with `w t ∈ U` for all `t`, and `w' : X → ℂ` with
`HasDerivAt (fun t => w t x) (w' x) t₀` for every `x`.

- `hasDerivAt_mem U hw hd`: `w' ∈ U`. Proof: write `w t x = ∑ᵢ cᵢ(t) bᵢ(x)` with
  `cᵢ(t) = ∑ₗ aᵢₗ w t (pᵢₗ)` by `exists_decomposition`; this sum has derivative
  `∑ᵢ (∑ₗ aᵢₗ w'(pᵢₗ)) bᵢ(x)` at `t₀`, so by uniqueness of derivatives
  `w' = ∑ᵢ (∑ₗ aᵢₗ w'(pᵢₗ)) bᵢ ∈ U`.
- `map_hasDerivAt L U hUV hw hd y`: the function `t ↦ (L (w t))(y)` has derivative
  `(L w')(y)` at `t₀`. Proof: both are the same finite linear combination of the values at the
  points `pᵢ` given by `exists_map_eval_sum`.

### Families in a finite-dimensional subspace

The same statements for families `w : K → V` of elements of a submodule `V` of `X → ℂ`
(rather than of functions), taking values in a finite-dimensional submodule `S` of `V`. They
are deduced from the statements above applied to the image `S.map V.subtype` of `S` in
`X → ℂ`, which is finite-dimensional.

- `coe_mem_map_subtype`: if `v ∈ S` then the underlying function of `v` lies in
  `S.map V.subtype`.
- `mem_of_integral μ M S hw hi hv`: if `M` is a further submodule of `V`, `w k ∈ S ⊓ M` for all
  `k`, the family is pointwise integrable, and `v ∈ V` is its pointwise integral
  (`v x = ∫ w k x dμ(k)` for all `x`), then `v ∈ M`. Proof: `integral_mem` for the
  finite-dimensional space `(S ⊓ M).map V.subtype`.
- `map_integral_of_mem μ L S hw hi hv y`: for `L : V →ₗ[ℂ] W`, `w k ∈ S` and `v` the pointwise
  integral of `w` as above, `(L v)(y) = ∫ (L (w k))(y) dμ(k)`; this is `map_integral`.
- `continuous_map_of_mem L S hw hc y`: if `k ↦ w k x` is continuous for every `x`, then
  `k ↦ (L (w k))(y)` is continuous; this is `continuous_map`.
- `map_hasDerivAt_of_mem L S hw hd y`: for `w : ℝ → V` with `w t ∈ S` and `v ∈ V` with
  `HasDerivAt (fun t => w t x) (v x) t₀` for every `x`, the function `t ↦ (L (w t))(y)` has
  derivative `(L v)(y)` at `t₀`; this is `map_hasDerivAt`.
- `hasDerivAt_mem_of_mem S hw hd`: in the same situation `v ∈ S`; this is `hasDerivAt_mem`.

### Joint continuity

- `continuous_uncurry_of_mem U hU hw hc`: let `K` and `X` be topological spaces, every element
  of `U` continuous, `w k ∈ U` for all `k`, and `k ↦ w k x` continuous for every `x`. Then
  `(k, x) ↦ w k x` is jointly continuous. Proof: by `exists_decomposition`,
  `w k x = ∑ᵢ (∑ₗ aᵢₗ w k (pᵢₗ)) bᵢ(x)`, a finite sum of products of a continuous function of
  `k` and a continuous function of `x`.
