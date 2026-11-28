# Open sets on which the analytified relation of an elementary chart is trivial

Let `K` be a complete ultrametric nontrivially normed field, `F` a presheaf on `K`-schemes,
and `y : Spec B → F` an affine test point with `B` finitely presented (presentation `Q`).
The model `M : ExistenceReduction.TestModel y y` represents `Spec B ×_F Spec B` in the
presheaf category on all `K`-schemes. See `SpaceChartRelation`.

- `ChartQuotient.etale_localizedHom`: the analytification `localizedHom K P Q f` of an
  algebra map `f` that is étale as a ring map is étale in the localized category (a
  restatement of `affineAnalytificationLocalizedEtaleReduction`).
- `ChartQuotient.isCompact_relationPreimage`: if `B ⊗_K B → M.C` (induced by `M.f`, `M.g`) is
  surjective, i.e. the model is closed in `Spec B ×_K Spec B`, then for every compact
  `N ⊆ Spec(B)ᵃⁿ` the set of points `r` of `Spec(M.C)ᵃⁿ` with both projections in `N` is
  compact.
- `ChartQuotient.exists_trivial_open` (**relation-trivial neighbourhoods**): assume moreover
  that `y` is étale and elementary at a prime `q` of `B`: for every `μ : M.C → B` with
  `μ ∘ M.f = id` and `μ ∘ M.g = id`, the only prime of `M.C` contracting to `q` along both
  projections is `μ⁻¹(q)`. Then every point `v` of `Spec(B)ᵃⁿ` with center `q` has an open
  neighbourhood `O` such that any two analytic maps `α, β : T ⟶ Spec(B)ᵃⁿ` with image in `O`
  that are related through `M` are equal.

## Proof

- `isCompact_relationPreimage`: let `S` be the set. Each `b ∈ B` has bounded seminorm on the
  compact `N`; hence every element of `B ⊗ B`, and by surjectivity every generator
  `M.R.map (X j)` of `M.C`, has seminorm bounded on `S` (by `pointSeminorm_baseMap` on pure
  tensors and subadditivity). So `S` lies in the image of one compact chart
  `chart K M.R m` (`mem_range_chart_iff`, `exists_radius_gt`), and `S` is closed, hence compact.
- `exists_trivial_open`: the diagonal `μ` (from the universal property) gives a section
  `δ = μᵃⁿ` of the étale map `(M.f)ᵃⁿ`, so `δ` is an open immersion
  (`localizedEtaleSectionsOpen`) with open image `Δ`. Every point `r` of `Spec(M.C)ᵃⁿ` over
  `(v, v)` lies in `Δ`: its center contracts to `q` along both projections
  (`center_baseMap`), so it is `μ⁻¹(q)` by the elementary hypothesis, and `r` is in the image
  of `baseMap μ` (`exists_baseMap_eq`). Take a compact chart image `N` that is a
  neighbourhood of `v` (`exists_chart`, `range_chart_mem_nhds`). The set `S ∩ Δᶜ` is compact
  (previous lemma, `Δ` open), so its image under `r ↦ (p₁ r, p₂ r)` is closed and misses
  `(v, v)`; choose open `U₁ ∋ v`, `U₂ ∋ v` with `U₁ × U₂` disjoint from it and set
  `O = U₁ ∩ U₂ ∩ int N`. If `α, β` land in `O` and `t` relates them, then every point of `t`
  lies in `Δ`, so `t` factors through `δ` (`openImmersion.exists_lift`), `t = σ ≫ δ`, and
  `α = σ = β`.

## Provenance

Derived. The compactness argument is that of Conrad–Temkin, *Non-archimedean analytification
of algebraic spaces* (2009), proof of Lemma 4.3.3, p.24
(`conrad-temkin-2009-nonarchimedean-analytification`): since `R → U × U` is topologically
proper, `R ∩ (K × K)` is compact for a compact neighbourhood `K` of `u`, so `u` has a
neighbourhood containing only finitely many points equivalent to it. Here the closedness of
the model in `Spec B ×_K Spec B` (separatedness) gives the compactness, and the elementary
hypothesis (Stacks Project, Decent Algebraic Spaces, Definition 68.11.5, Tag 0BGU,
`stacks-decent-spaces-chapter-ed88ff78-2026-11-05`) puts every point of the relation over
`(v, v)` on the diagonal, so the neighbourhood can be chosen with trivial relation.
