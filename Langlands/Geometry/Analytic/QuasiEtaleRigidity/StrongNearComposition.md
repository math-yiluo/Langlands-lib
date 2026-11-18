# Precomposition of the test relations and common strong representatives

Author: Worker 931.

This is a helper module of `QuasiEtaleLiftCompatibilityProof`. It develops the
Library's test relations `StrongNear` and `IsNear` from
`ContinuousAnalyticAction`, which formalize Berkovich's `d(φ, ψ) < (U, f, t)`
(Berkovich 1994, §6). All results are internal.

## Charts

- `exists_chart_mem`: every point of a saturated presentation lies in a chart.
- `exists_chart_mem_subset_inter`: a point of the intersection of two charts lies
  in a chart contained in both. This is the net property of the chart family.
- `exists_subchart_image_subset`: for a strong map `c`, a source chart `k`, a
  point `y ∈ k` and a target chart `i` containing `c y`, there is a chart
  `k' ∋ y` inside `k` with `c(k') ⊆ i`. The proof combines the net property of
  the target with `StrongHom.exists_chart_inter_preimage`.
- `exists_restriction_comap_eq`: a point of a chart that lies in a smaller chart
  comes from the spectrum of the smaller chart through the restriction map.
- `comp_pullback_eq` and `restriction_comp_pullback`: the pullback of a composite
  through an intermediate chart, and the restriction of a pullback to a smaller
  source chart.

## Precomposition

`StrongNear.precomp`: if `StrongNear τ a b` and `c : S ⟶ T` is any strong map,
then `StrongNear τ (c ≫ a) (c ≫ b)`. The preimages agree trivially. For the
covering, `exists_subchart_image_subset` gives a chart of `S` mapped into a test
piece of `a, b`. For the bound at a test piece `k` of the composites and a
point `p`, take the point `y` of `k`. There is a subchart `k' ∋ y` mapped by
`c` into a test piece `i` of `a, b`, and `p` comes from a point `p'` of `k'`.
The pullbacks of the composites restricted to `k'` factor through `i`.
Therefore the value at `p` equals the value of `a` and `b` at the point
`comap (c.pullback k' i) p'` of `i`, which is bounded by hypothesis.

## Localized form

The lemmas about arrows between images of saturated presentations are stated
for `localizationFunctor.obj A`, where rewriting is syntactic. They apply to
arbitrary objects through the definitional identification of `X` with
`localizationFunctor.obj (presentationOf X)`.

- `fraction_eq_iff` and `isNear_iff_numerators`: `IsNear τ φ ψ` holds iff there
  are a quasi-isomorphism `s : T ⟶ presentationOf Y` and strong maps `a`, `b`
  with `map s ≫ φ = map a`, `map s ≫ ψ = map b` and `StrongNear τ a b`.
- `exists_numerator_precomp`, `numerator_precomp` and `IsNear.precomp`: if
  `IsNear τ φ ψ`, then `IsNear τ (f ≫ φ) (f ≫ ψ)` for every morphism `f`. The Ore
  refinement comes from the Library's `exists_commonStrongNumerators`.
- `exists_common_quasiIso_refinement`: two quasi-isomorphisms to one target have
  a common quasi-isomorphic refinement. This uses the Library's
  `quasiIsoOreInclusion` and `quasiIsoOreLift`.
- `numerator_eq_comp`: numerators of one localized arrow on comparable
  refinements agree. This uses faithfulness, the Library's
  `localizationFunctor_map_injective`.
- `NearNumerators`, `exists_strongNear_numerators_aux` and
  `exists_strongNear_numerators`: let `E` be a finite set of test triples with
  `IsNear τ ψ ψ₁` and `IsNear τ ψ ψ₂` for all `τ ∈ E`. Then one quasi-isomorphic
  refinement `s` of the source carries strong numerators `x₀, x₁, x₂` of
  `ψ, ψ₁, ψ₂` with `StrongNear τ x₀ x₁` and `StrongNear τ x₀ x₂` for every
  `τ ∈ E`. The proof is by induction on `E`. At each step it refines by
  `exists_common_quasiIso_refinement`, identifies numerators by
  `numerator_eq_comp`, and transports the relations by `StrongNear.precomp`.
