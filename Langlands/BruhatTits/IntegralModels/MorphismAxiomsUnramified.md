# KP Axiom 4.1.22 for a model family described over the maximal unramified integers

This module proves the complete KP Axiom 4.1.22, `Q.SatisfiesMorphismAxioms ρ`,
for a building model family `M` over `↥𝒪[F]` whose neutral models have the
specified integral points over the maximal unramified integers. The main
theorem takes six statements as hypotheses.

- `UnramifiedModelKernelStatement` (KP Proposition 8.4.15 over the
  integers of the maximal unramified extension);
- the five facet-clause statements
  `UnramifiedFacetParabolicImageStatement`,
  `UnramifiedFacetParabolicOrderStatement`,
  `UnramifiedFacetCommonTorusStatement`,
  `UnramifiedFacetRootDatumStatement` and
  `UnramifiedFacetPositiveRadicalStatement`.

Throughout, `fixedFieldIntegers F` are the integers of the maximal unramified
extension `inertiaFixedField F`. The module installs the coefficient algebra
`↥𝒪[F] → fixedFieldIntegers F` and its scalar tower, from Mathlib's
`Valuation.HasExtension` instances, under the names
`morphismAxiomsUnramifiedAlgebra` and `morphismAxiomsUnramifiedScalarTower`.
These are the instances that define `IntegralModel.baseChangeUnramified`.

## Declarations

- `BuildingModelFamily.exists_satisfiesMorphismAxioms_of_unramified`. Let
  `P : ParahoricBuildingData G`, a realization `R` and a splitting `T`
  satisfy the seven predicates of the target statement
  `IntegralModelAxiomsStatement`. Let `C`, `A`, `e`, `a` satisfy the eight
  conclusions of the apartment-compatible unramified descent:
  - `e` is injective and equivariant along `rationalExtend`;
  - `e (apartmentMap w) = C.apartmentMap (a w)`;
  - every image point of `e` is Galois-fixed, and every Galois-fixed point is
    an image point;
  - `e` reflects special points;
  - `a` pulls facets of `C` back to facets;
  - the character-valuation kernel of the base-changed `S` fixes the image of
    the apartment.

  These are the same hypotheses as in the five facet statements. Let `E` be an
  unramified zero datum, and let `M` be a building model family over `↥𝒪[F]`
  with two properties:
  - `hpoints`: for every index `Ω`, the base change of the neutral model of
    `M.model Ω` to `fixedFieldIntegers F` has integral points
    `E.zeroPoints ⊓ C.pointwiseFixer (e '' Ω)`;
  - `htorus`: every integral torus `M.torus Ω g Ωa h` satisfies the torus
    clause of Axiom 4.1.20(3).

  Then the six statements imply that there are special-fibre quotient data
  `Q : BuildingModelQuotientFamily P.toValuationBuildingData M` and relative
  root reflection data `ρ : RelativeRootReflectionData P.toValuationBuildingData.i`
  with `Q.SatisfiesMorphismAxioms ρ`.

## Proof

The quotient family `Q` is chosen facet by facet with the Library theorem
`SpecialFibreQuotientData.exists_isReductiveQuotient` (module
`Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence`), applied to
the relative-component model of each facet. Every `Q.quotient F` is the maximal
reductive quotient of the special fibre of the neutral facet model. The residue field of
`𝒪[F]` is perfect by instance search. The data `ρ` come from the Library
theorem `relativeRootReflectionExistence`, applied to the connected reductive
group `G` and the maximal split torus `P.toValuationBuildingData.i`. Both are
fields of `ValuationBuildingData`.

The general morphism clauses are
`satisfiesGeneralMorphismAxioms_of_unramified_of_axioms` (module
`GeneralMorphismAxiomsUnramified`), applied to `hpoints` and the two
compatibilities of `e`.

For the facet clauses, the facet model of a facet `F` is
`M.model (BuildingModelIndex.ofFacet F)`. Its neutral model is smooth by the
structure field `neutral_smooth`. `hpoints` at `ofFacet F` gives its integral
points `E.zeroPoints ⊓ C.pointwiseFixer (e '' F)`. Each field of
`FacetAxiomClauses` is then filled in as follows:

- `reductive_quotients`: the property of `Q` above.
- `parabolic_images` and `reduction_preimages`: the two conjuncts of
  `UnramifiedFacetParabolicImageStatement`, applied to the models of `F` and
  `F'` and to the family morphism `M.facetModels.morphism F F' h`.
- `common_tori`: take a common chart `g`, `Fa`, `Fa'` and the torus
  `M.torus (ofFacet F') g Fa' hF'`. `htorus` gives that it is closed and split
  (`IsClosedSplit`) and that its special fibre is maximal split in the neutral
  special fibre of `F'`. `UnramifiedFacetCommonTorusStatement` gives the two
  remaining conjuncts of `HasMaximalSplitTori`: the torus is maximal split in
  the neutral special fibre of `F` and in `Q.quotient F`, through the family
  morphism.
- `lie_weight_signs`: the third conjunct of
  `UnramifiedFacetCommonTorusStatement`, for the same data.
- `parabolic_order`: `UnramifiedFacetParabolicOrderStatement` applied to
  `M.facetModels`, whose facet models all have the required integral points.
- `derivative_root_data`: `UnramifiedFacetRootDatumStatement` applied to the
  facet model, `Q.quotient F`, the torus `M.torus (ofFacet F) g Fa hF` and `ρ`.
  The statement quantifies over every relative root reflection datum, so the
  choice of `ρ` does not matter.
- `positive_radicals`: the reductions of both neutral models are surjective by
  the Library theorem `IntegralModel.reduction_surjective` for smooth models
  over a Henselian local ring. `𝒪[F]` is Henselian by the Library theorem
  `henselianLocalRing_integer` (module `DepthZeroInduction`). The inclusion of
  positive subgroups is `UnramifiedFacetPositiveRadicalStatement`.

Elaborating the applications of the six statements, with their long
preambles, needs a heartbeat budget of 4,000,000, set locally on the theorem.

## Provenance

KP prove Axiom 4.1.22 for their Bruhat–Tits group schemes in §8.4 over the
maximal unramified extension and descend it in §9.5 (Kaletha–Prasad,
*Bruhat–Tits theory: a new approach*, Axiom 4.1.22, printed pp. 163–164).
This module assembles the clauses using the six statements and the results
named above. The construction in `ModelAxiomsUnramified` provides the
integral point description `hpoints` and the torus clause `htorus`.
