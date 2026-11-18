# Conditional construction of the point family of an analytification

Internal conditional construction (derived provenance) following the route of Conrad–Temkin
(2009), §4.2–4.3: define the analytification of `X` through the analytic quotient of its
étale affine charts and étale descent of morphisms. It is formalized against the Library's
localized category `LocalizedCategory.{u,u,u}`.

## Hypothesis bundles

- `AnalyticInputs K` is a `Prop`-valued structure of explicit, unproved analytic inputs over
  `K`:
  - `sheaf`: Worker 790's proposed `EtaleHomSheafStatement`;
  - `descent`: Worker 550's proposed `LocalizedEtaleSourceDescentStatement`, with the index type in
    `Type u`;
  - `comp` and `id`: the composition and identity clauses of the Library's
    `AffineAnalytificationLocalizedFunctorialityStatement`;
  - `affPullback`: presheaf fibre squares of affine tests over an affine test go to pullback
    squares. `SpaceAnalytificationExistenceAffinePullbacks` derives it from the Library's
    `AffineAnalytificationFibreProductStatement`;
  - `etaleFwd`: analytifications of étale algebra maps are étale (Berkovich 1990,
    Proposition 3.4.6(3));
  - `base`: the Library's `LocalizedEtalePullbackStatement`;
  - `points`: in a pullback square with an étale leg, matching pairs of underlying points
    lift to the pullback;
  - `surj`: a family of algebra maps jointly surjective on prime spectra has analytified maps
    jointly surjective on points (Berkovich 1990, Proposition 3.4.6(7) and the fibre
    isomorphism (*) in its proof).

  Nothing in this module proves these inputs.
- `ChartData X`: a family of étale affine test points `xᵢ : Spec Aᵢ → X`, with finite
  polynomial presentations. For every test point `y : Spec B → X` and every prime `𝔭` of `B`,
  some chart has the property that every model of `Spec B ×_X Spec Aᵢ` has a prime over `𝔭`.
  `nonempty_chartData` (module `SpaceAnalytificationExistenceCharts`) constructs such data.
- `QuotientData D`: an analytic quotient of the analytified charts. It consists of `Y`,
  étale maps `πᵢ : Spec(Aᵢ)ᵃⁿ → Y` jointly surjective on points, and the condition that chart
  fibre squares go to pullbacks. It is the conclusion of `SpaceAnalytificationChartQuotientStatement`.

## Construction and proofs

- `chart_compat`: if `ty α ≫ xᵢ = ty β ≫ xⱼ` for algebra maps `α : Aᵢ → Z` and
  `β : Aⱼ → Z`, then `loc α ≫ πᵢ = loc β ≫ πⱼ`. Factor `(α, β)` through the model of
  `Spec Aᵢ ×_X Spec Aⱼ`, then use functoriality and the commutativity of the chart quotient
  square.
- For a test point `y : Spec B → X`, `coverModel` chooses the model
  `(Nⱼ, fⱼ : B → Nⱼ, gⱼ : Aⱼ → Nⱼ)` of `Spec B ×_X Spec Aⱼ`.
  - `coverMap j = loc fⱼ` is étale (`etale_f` and `etaleFwd`) and jointly surjective
    (`ChartData.cover` and `surj`).
  - `ext_of_cover` checks equality of maps out of `Spec(B)ᵃⁿ` on this cover
    (`hom_ext_of_etale_cover`).
- `pointMap` glues `coverValue j = loc gⱼ ≫ πⱼ` along the cover (`exists_glue_of_etale_cover`).
  For compatibility on arbitrary `V`, a pair of maps into `Nⱼᵃⁿ` and `Nₖᵃⁿ` that agree over
  `Spec(B)ᵃⁿ` factors through the analytification of the model of `Spec Nⱼ ×_{Spec B} Spec Nₖ`
  (`affPullback`). On it, `chart_compat` applies.
- `localizedHom_pointMap` is the key identity `loc β ≫ pointMap y = loc α ≫ πᵢ` whenever
  `ty β ≫ y = ty α ≫ xᵢ`. It is checked on the cover of the source through the model
  universal property, `coverMap_pointMap` and `chart_compat`.
- `pointFamily` collects the maps into a `PointFamily`. It satisfies:
  - `pointFamily_naturality` (by `ext_of_cover` and `localizedHom_pointMap`);
  - `pointFamily_etale` (by `descent`, since each `coverMap j ≫ pointMap` is
    `loc gⱼ ≫ πⱼ`, étale by `etale_g`, `etaleFwd` and `etale_comp`);
  - `pointFamily_chart` (`pointMap xᵢ = πᵢ`, by `localizedHom_pointMap` with identities);
  - `pointFamily_jointly_surjective` (from `QuotientData.surj`).
