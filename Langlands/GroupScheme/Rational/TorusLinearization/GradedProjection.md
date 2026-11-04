# Projections onto graded subspaces that respect the grading

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
Internal machinery only. Everything is in namespace
`Langlands.GroupScheme.TorusLinearization`.

Setting: `K` a field, `V` a `K`-vector space, and `c : M → V →ₗ[K] V` a family of
component projections indexed by `M`. They satisfy:

- orthogonality: `c ψ (c χ v) = if χ = ψ then c χ v else 0` (hypothesis `hcc`);
- completeness: each `v` is the sum `∑ χ ∈ s, c χ v` over some finite set `s`
  (hypothesis `hfin`).

## Statements

- `graded_apply_of_mem_range hcc hx χ`: if `x` lies in the range of `c ψ`, then
  `c χ x = if ψ = χ then x else 0`.
- `graded_apply_eq_zero_of_not_mem hcc hs hψ`: if `∑ χ ∈ s, c χ v = v` and
  `ψ ∉ s`, then `c ψ v = 0`.
- `exists_graded_projection c hcc hfin Y hY`: let `Y` be a subspace with
  `c χ y ∈ Y` for all `χ` and all `y ∈ Y`. Then there is a linear map
  `π : V →ₗ[K] V` such that
  - `π y = y` for `y ∈ Y`,
  - `π v ∈ Y` for all `v`,
  - `π (c χ v) = c χ (π v)` for all `χ` and `v`.

## Proof of `exists_graded_projection`

For each `χ`, let `Y_χ := Y ⊓ range (c χ)`. Choose a linear left inverse
`g_χ : V → Y_χ` of the inclusion (`LinearMap.exists_leftInverse_of_injective`).
Let `q_χ : V → V` be `g_χ` followed by the inclusion. Then `q_χ` maps into `Y_χ`
and fixes `Y_χ` pointwise.

By orthogonality and completeness, `c χ v = 0` for `χ` outside the finite set
`s v` chosen for `v`. So `v ↦ (χ ↦ c χ v)` is a linear map `D : V → (M →₀ V)`,
built with `Finsupp.onFinset`. Set `π := Finsupp.lsum K q ∘ₗ D`, that is,
`π v = ∑_χ q_χ (c χ v)`. This sum may be taken over any finite set outside which
the components of `v` vanish.

- If `y ∈ Y`, each `c χ y` lies in `Y_χ`, so `q_χ (c χ y) = c χ y`. Hence
  `π y = ∑ χ ∈ s y, c χ y = y`.
- Each `q_χ (c χ v)` lies in `Y_χ ⊆ Y`, so `π v ∈ Y`.
- The components of `c χ v` vanish outside `{χ}`, so
  `π (c χ v) = q_χ (c χ (c χ v)) = q_χ (c χ v)`. On the other side, each
  `q_ψ (c ψ v)` lies in the range of `c ψ`. Hence `c χ` kills it for `ψ ≠ χ` and
  fixes it for `ψ = χ`. Thus `c χ (π v) = q_χ (c χ v)` when `χ ∈ s v`. When
  `χ ∉ s v`, both sides are `0` because `c χ v = 0`.

## Provenance

This is elementary linear algebra and is internal to this project. It is an abstract
analogue of a step in the proof of Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
2nd ed., Proposition B.4.2, printed p.577 (PDF p.603). There, complete reducibility
of linear representations of a torus gives a torus-stable complement of the
subspace `V'_1` in `V'`. Here the representation is replaced by a graded vector
space, and the complement is the kernel of `π`.
