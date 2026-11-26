# Integral models with Axioms 4.1.20 and 4.1.22 on supplied building data

The module `Langlands.Geometry.Building.IntegralModelAxiomsProof` proves
`Langlands.Geometry.Building.integralModelAxioms` of type
`IntegralModelAxiomsStatement.{u}` at arbitrary universe `u`. For the
supplied `P`, `R` and `T` under the seven predicates of the corrected
Section 4.2 axioms, it gives an integral model family `M` over `𝒪[F]`,
special-fibre quotient data `Q` for its facet models and relative root
reflection data `ρ`. The two conclusions are `M.SatisfiesModelAxioms P`
and `Q.SatisfiesMorphismAxioms ρ`. [Statement](IntegralModelAxiomsStatement.md)

## Proof

The Lean theorem applies
`integralModelAxiomsStatement_of_unramified_remaining` to
`unramifiedApartmentDescent` and `unramifiedZeroDescent`. For `K` the
maximal unramified extension of `F`, the first theorem gives an injective
equivariant embedding `e` of the supplied building onto the Galois-fixed
locus and a compatible affine apartment map, with the special-point, facet
and torus clauses. The second gives Galois stability of the upstairs
subgroups and `G(F)^0 = G(K)^0 ∩ G(F)`.
[Apartment descent](UnramifiedApartmentDescentProof.md),
[Zero-subgroup descent](UnramifiedZeroDescentProof.md)

The construction transports each nonempty bounded apartment subset and
each facet `Ω` to `e '' Ω`. The theorem `unramifiedParahoricModel` gives
the full and neutral models there over the integers of `K`. The
full model's integral points are Galois-stable, so
`unramifiedSmoothModelDescent` descends it to `𝒪[F]`. Taking its relative
identity component gives the neutral model, whose unramified integral
points are identified by
`RelativeComponentModelData.baseChange_neutral_integralPoints_eq`. The
full and neutral points over `𝒪[F]` are the pointwise fixers of `Ω` in
`G(F)^1` and `G(F)^0` by pullback along `G(F) → G(K)`.

The proof constructs the morphisms from inclusions of upstairs integral
points using `unramifiedSmoothHomExtension`. The results
`unramifiedOneFixerClosure` and `unramifiedZeroFixerAffineRoot` give the
closure and facet comparisons. The theorem `unramifiedTorusClause` gives
the closed split integral tori and their maximal split special fibres.
For simply connected `G`, `UnramifiedZeroDatum.zeroPoints_eq_top_of_isSimplyConnected`
gives equality of the upstairs full and neutral fixers. The extension theorem
then gives a morphism from the full model to the neutral one, inverse to
its inclusion by generic-fibre rigidity. These constructions give
`M.SatisfiesModelAxioms P`. [Model family](../../BruhatTits/IntegralModels/ModelAxiomsUnramified.md)

The proof chooses `Q` by `SpecialFibreQuotientData.exists_isReductiveQuotient`
and `ρ` by `relativeRootReflectionExistence`. For the general morphism
clauses it descends smoothness, connectedness and unipotence of the
special-fibre kernels from `unramifiedModelKernel`. A unipotent kernel
ensures that the special-fibre map induces a closed immersion on each torus.
For incident facets it applies
`unramifiedFacetParabolicImage_of_generation_positive_modelKernel` to
`unramifiedUpstairsRadicalRootGeneration`, `unramifiedFacetPositiveRadical`
and `unramifiedModelKernel` for the parabolic image and the reduction
preimage. The remaining fields use `unramifiedFacetCommonTorus`,
`unramifiedFacetParabolicOrder`, `unramifiedFacetRootDatum` and
`unramifiedFacetPositiveRadical`, with surjectivity of smooth reduction over
the Henselian valuation ring. This gives `Q.SatisfiesMorphismAxioms ρ`.
[Morphism axioms](../../BruhatTits/IntegralModels/MorphismAxiomsUnramified.md),
[Unramified assembly](../../BruhatTits/IntegralModels/IntegralModelAxiomsConditional.md)

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
  Axioms 4.1.20 and 4.1.22 are on printed pp. 163–164 / PDF pp. 194–195.
  Theorems 8.3.2 and 8.3.13 construct the models over the maximal unramified
  integers. Section 9.2.5 descends them and §9.5 checks the axioms. The
  kernel input is the smooth connected unipotent assertion of Proposition
  8.4.15. Its Lean proof uses an ordered open cell indexed by all indivisible
  roots and a torus factor. [KP source ledger, Bundle D](../../../notes/bruhat-tits/kp-source-ledger.md#bundle-d-models-descent-and-the-actual-reduction-map)
- Kaletha–Prasad, *Corrections and additions* (1 November 2024),
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
  PDF pp. 27–28 give the corrected Chapter 4 axioms. PDF pp. 37–38 specify
  the perfect residue field hypothesis, correct the proof of Theorem
  8.3.13 and set up the morphism in Proposition 8.4.15. The residue field
  of the local field `F` is finite and hence perfect.
