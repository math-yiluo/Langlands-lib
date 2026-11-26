# Facets of an apartment: nonempty, bounded, inside the closure of a coface; chart-independent boundedness

This helper module proves elementary facts about the facets of the apartment of
a `ValuationBuildingData`. Facets here are the Library's sign classes
(`AffineRootSystem.facet`: points where every affine root has the same sign;
compare Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, Remark 1.3.16).
It also proves that boundedness of a subset of `B(G)` does not depend on the
apartment chart used to present it. The construction of the integral-model
family (KP Axioms 4.1.20 and 4.1.22) uses these consequences of the
affine root-system and building axioms.

## Torsor results for affine root systems

The apartment `B.Apartment` is an affine space over the real vector space
`TranslationSpace B.i`, which has no chosen norm. The Library's
`IsAffineRootSystemWithRankZero.exists_parallel_roots_opposite_sign` and
`isCompact_facetClosure` (in `AffineFacetCompactness`) need a normed vector space.
`facetClosure_subset_closure_facet` (in `FacetClosureUnionClosedProof`) needs a
metric torsor. The results below are versions of these facts for a general affine
space `A` over a real vector space `V`. They copy the Library arguments.

- `IsFacet.nonempty`: a facet is the class of one of its points, so it is
  nonempty.
- `IsAffineRootSystemWithRankZero.exists_parallel_roots_opposite_sign_of_torsor`:
  for an affine root system `Ψ` (rank zero allowed), a point `p` and `ψ ∈ Ψ`,
  there are `η, χ ∈ Ψ` with the same derivative as `ψ` and `η p < 0 < χ p`.
  The proof is the Library proof. The fiber of `ψ.linear` is infinite. Only
  finitely many roots are bounded at `p`, so the fiber has a root `η` with
  `|η p| > 2|ψ p| + 1`. Reflecting `η` by the coroot of `ψ` and negating gives
  `-(η - 2ψ) ∈ Ψ`, whose value at `p` has the opposite sign.
- `IsAffineRootSystemWithRankZero.exists_bound_span_facetClosure`: every
  linear form in the span of the derivative roots is bounded in absolute value on
  the vectors `y -ᵥ p` for `y` in the closed facet `facetClosure Ψ p`. For a
  derivative `ψ.linear`, take `η, χ` as above. On the closed facet, `η ≤ 0` and
  `χ ≥ 0`, which gives the bound `|η p| + |χ p|`. Sums and scalar multiples
  are then handled by span induction.
- `IsAffineRootSystemWithRankZero.exists_bound_facetClosure`: the derivative
  roots span the dual (part of `IsAffineRootSystemWithRankZero`), so every real
  affine functional is bounded in absolute value on every closed facet.
- `IsAffineRootSystemWithRankZero.bddAbove_image_of_isFacet`: hence every real
  affine functional is bounded above on every facet.
- `facetClosure_subset_closure_facet_of_continuous`: take any topology on `A`
  in which a map `g : ℝ → A` is continuous as soon as `f ∘ g` is continuous
  for every real affine functional `f`. In such a topology the closed facet of
  `p` lies in the closure of the facet of `p`. The proof is the Library proof:
  the points `lineMap q p t` with `0 < t ≤ 1` lie in the facet of `p` and tend
  to `q` as `t → 0⁺`.

## Results for the apartment of `B`

Here `B : ValuationBuildingData G` and the topology is the Library's
`affineApartmentTopology B` (the initial topology of all real affine
functionals). `apartmentClosure B` is the ordinary closure for this topology.

- `continuous_of_forall_affineApartmentFunctional`: a map into `B.Apartment` is
  continuous for `affineApartmentTopology B` if its composite with every real
  affine functional is continuous. This is the universal property of an initial
  topology.
- `facetClosure_subset_apartmentClosure_facet`: the closed facet of `x` for
  `B.affineRoots` lies in `apartmentClosure B (facet B.affineRoots x)`.
- `subset_apartmentClosure_of_isFaceOf`: if `Fa` is a face of `Fa'` for
  `B.affineRoots` (`IsFaceOf`: `Fa'` is a facet `facet x` and `Fa` lies in
  `facetClosure x`), then `Fa ⊆ apartmentClosure B Fa'`. No building axiom is
  used.
- `nonempty_of_isFacet`: a facet of the apartment of `B` is nonempty.
- `isBoundedSubset_of_isFacet`: suppose `B.affineRoots` satisfies
  `IsAffineRootSystemWithRankZero`. Then every facet `Fa` of `B.affineRoots`
  satisfies `B.IsBoundedSubset Fa`, i.e. every real affine functional is
  bounded above on `Fa`.
- `isBoundedSubset_of_isFacet_of_satisfiesApartmentAxioms`: the same
  conclusion under `B.SatisfiesApartmentAxioms`. Its fourth component in
  `ValuationBuildingData.satisfiesApartmentAxioms_iff` is
  `IsAffineRootSystemWithRankZero B.affineRoots`.

## Boundedness does not depend on the apartment chart

`B.translatedApartmentMap g x = g • B.apartmentMap x` is the chart of the
apartment `g · A(S)`. A subset of `B(G)` can have presentations in several
charts. `B.IsBoundedSubset` is defined on one chart, so a separate argument is
needed when a subset is bounded in one presentation and another presentation is
used.

- `isBoundedSubset_of_image_translatedApartmentMap_eq`: assume
  `B.HasNormalizerApartmentStabilizer` (the stabilizer of `A(S)` in `G(F)` is
  `N(F)`), injectivity of `B.apartmentMap`, and that for all `g, h` some
  `k ∈ G(F)` maps `h · A(S)` onto `g · A(S)` and fixes
  `h · A(S) ∩ g · A(S)` pointwise. If
  `B.translatedApartmentMap g '' X = B.translatedApartmentMap h '' Y` and
  `B.IsBoundedSubset Y`, then `B.IsBoundedSubset X`.
  Proof: `(k h) · A(S) = g · A(S)`, so `g⁻¹ k h ∈ N(F)`
  (`smul_apartmentImage_eq_iff`). The Library's affine chart transition
  `ν = B.apartmentChartTransition (k * h) g` satisfies
  `g · ν(y) = (k h) · y = k · (h · y)` (`translatedApartmentMap_transition`,
  `translatedApartmentMap_mul`). For `y ∈ Y` the point `h · y` lies in both
  apartments, hence is fixed by `k`, so `g · ν(y) = h · y`. Injectivity of the
  chart `g` gives `X = ν '' Y`. For a real affine functional `f`, `f ∘ ν` is a
  real affine functional, which is bounded above on `Y`.
- `isBoundedSubset_of_image_translatedApartmentMap_eq_of_axioms`: the same
  conclusion for `B = P.toValuationBuildingData` under the seven predicates of
  the target statement (`SatisfiesBuildingAxiom R`, `HasBoundedOpenStabilizers`,
  `SatisfiesAffineApartmentAxiom T`, `HasRootReflections`,
  `SatisfiesApartmentAxioms`, `HasCompatibleApartmentFacets`,
  `HasTitsSystem`). The stabilizer clause is the field
  `normalizerApartmentStabilizer` of `SatisfiesBuildingAxiom`, injectivity is
  the field `injective` of `HasCompatibleApartmentFacets`, and the conjugacy
  property is the Library theorem `apartmentConjugacyFixingIntersection`
  (KP Proposition 4.2.24 on these supplied data).
