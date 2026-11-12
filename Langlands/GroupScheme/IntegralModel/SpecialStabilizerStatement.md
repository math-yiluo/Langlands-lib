# The supplied-model special-stabilizer identity

This module states `Langlands.GroupScheme.IntegralModel.SpecialStabilizerStatement`
and proves that it, together with the published
`Langlands.Geometry.Building.RootValuationBuildingConstructionStatement`,
implies the published construction target
`Langlands.GroupScheme.IntegralModel.BuildingComparisonStatement`.
The statement is a proposition. Nothing in this module proves it.

## The statement

`SpecialStabilizerStatement.{u}` is universe polymorphic. At each universe `u`
it ranges over:

* every `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
  `IsNonarchimedeanLocalField F`, in equal and mixed characteristic;
* every actual group scheme `G` over `Spec F` with a proof
  `hG : IsConnectedReductive G`;
* every supplied `M : IntegralModel 𝒪[F] F G`, with its own generic
  identification `M.genericIso`, whose full actual special-fibre pullback
  `(GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group` is
  connected reductive.

These are exactly the binders and the special-fibre hypothesis of
`BuildingComparisonStatement`. As there, the instance `IsAffineHom G.X.hom`
is derived from `hG`; it is not a premise.

The statement then quantifies over every `P : ParahoricBuildingData G`, every
polysimplicial realization `R` and apartment splitting `T` of
`P.toValuationBuildingData`, and proofs of the seven predicates that form the
conclusion of `RootValuationBuildingConstructionStatement`:

* `P.SatisfiesBuildingAxiom R` (KP Axiom 4.1.1);
* `P.HasBoundedOpenStabilizers` (KP Axiom 4.1.2);
* `P.SatisfiesAffineApartmentAxiom T` (KP Axiom 4.1.4);
* `P.HasRootReflections`, `P.SatisfiesApartmentAxioms` and
  `P.HasCompatibleApartmentFacets` (KP Axiom 4.1.6);
* `P.HasTitsSystem` (KP Axiom 4.1.9).

Its conclusion is that there exists a point `y : P.ReducedBuilding` of the
existing quotient (7.6.2) such that

* `P.IsSpecialPoint y`: `y` is a `G(F)`-translate of the image of a special
  point of the apartment, for the existing affine roots of `P`; and
* `M.integralPoints = P.compactStabilizer y`: the original image of the
  integral sections of `M` in `rationalPoints G` equals
  `K_y = G(F)^1 ∩ G(F)_y`. Here `G(F)^1` is the actual common kernel
  `rationalCommonNormKernel G` of the absolute values of the rational
  characters, and `G(F)_y` is the stabilizer of `y` for the existing action of
  `rationalPoints G` on the quotient.

No smoothness of `M`, splitness, rank, residue-size, chosen torus, comparison,
unique-fixer, maximality or Iwasawa hypothesis is added. The building data
`P`, `R`, `T` and the seven predicates are hypotheses, quantified universally:
the statement must hold for every datum that satisfies them.

## Source correspondence

The statement is derived from the following original assertions.

* Bruhat–Tits, *Groupes réductifs sur un corps local II* (1984), registered as
  `bruhat-tits-1984-reductive-local-groups-ii`, Proposition 5.1.40, printed
  p. 161 / PDF p. 158. A smooth model `𝔊` over the base integers with generic
  fibre `G` has reductive closed fibre if and only if `G` splits over the
  strict Henselization and there is a point `x` of the base-field building,
  special as a point of the building over the strict Henselization, with
  `𝔊 ≅ 𝔊_x`. Proposition 4.6.28(i), printed p. 135 / PDF p. 132, identifies
  `𝔊_x(𝒪)` with the fixer of `x` in `G^1`. Together these give
  `M(𝒪) = 𝔊_x(𝒪) = G(F)^1 ∩ G(F)_x`, the subgroup `P.compactStabilizer y`
  at the point `y` corresponding to `x`. Smoothness of `M` is not a premise
  here: the Library proves it from the two connected-reductivity hypotheses
  (`IntegralModel.isSmooth_of_reductive_localField`).
* Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, Theorem 9.9.3(2), printed
  pp. 380–381 / PDF pp. 411–412, gives the same identification in their
  conventions: a reductive `𝒪`-model is `𝒢_x^0` for a hyperspecial point `x`
  of `B(G)`. Proposition 9.9.2, printed p. 380 / PDF p. 411, shows that a
  point of `B(G)` special in the building over the maximal unramified
  extension is special in `B(G)`.
* The sources prove these assertions for *the* Bruhat–Tits building of `G`.
  The statement instead quantifies over every `ParahoricBuildingData G`
  satisfying the seven predicates. The apartment class of such a datum is
  `ω`-compatible (`isOmegaCompatible`), and Kaletha–Prasad Proposition 6.2.6,
  printed p. 216 / PDF p. 247, shows that any two `ω`-compatible valuations of
  the root datum are equipollent. The Library proves this as
  `omegaCompatibleApartmentUniqueness`. So the quotient of every such datum is
  the Bruhat–Tits building of `G` built from its own maximal split torus. This
  is why the universal quantification over `P` agrees with the sources, rather
  than being an extra assumption about the data.

The provenance is derived: the statement combines the cited assertions and
is stated on the Library's existing quotient and subgroups. It is not a
verbatim source theorem.

## The constructor and the reduction

`BuildingComparison.ofParahoricSpecialPoint` constructs a `BuildingComparison M`
from `P`, `R`, `T`, the seven predicates, an arbitrary point
`y : P.ReducedBuilding` with `P.IsSpecialPoint y`, and the equality
`M.integralPoints = P.compactStabilizer y`. Unlike the published
`ofParahoricApartmentSpecialPoint`, the point `y` need not lie in the image of
the standard apartment.

* The building is exactly `P.toValuationBuildingData`, as the simplification
  theorem `ofParahoricSpecialPoint_building` records. The distinguished point
  is exactly `y` (`ofParahoricSpecialPoint_point`).
* The metric is selected by classical choice from the published
  `metricRealization`, applied to the seven predicates. It is a complete,
  nonpositively curved metric on the existing quotient. The existing
  rational-point action is isometric and its orbit maps are continuous for
  `rationalPointTopology F G.X`.
* Vertexhood: write `y = g • P.apartmentMap x` with `x` special in the
  apartment. The published `AffineRootSystem.isVertex_of_isSpecialPoint`, for
  the affine root system supplied by `P.SatisfiesApartmentAxioms`, makes `x` an
  apartment vertex. `isVertex_apartmentMap` and `IsVertex.smul` translate this
  to `y`.
* The special-point field is the premise, and the subgroup equality is the
  supplied equality.
* Uniqueness: if `z` is fixed by every element of `M.integralPoints`, it is
  fixed by every element of `P.compactStabilizer y`, by the supplied
  equality. The published
  `ValuationBuildingData.eq_of_compactStabilizer_fixed_of_special_buildingPoint`
  then gives `z = y`. Its inputs are the apartment axioms, actual opposite
  factor pairs (the published `ParahoricBuildingData.hasOppositeFactorPairs`),
  apartment-map injectivity (`hC.injective`) and common apartments, which
  `PolysimplicialRealization.hasCommonApartmentWith_of_isBuilding` derives from
  the building axiom.

`buildingComparisonStatement_of_specialStabilizer` proves
`BuildingComparisonStatement.{u}` from proofs of
`RootValuationBuildingConstructionStatement.{u}` and
`SpecialStabilizerStatement.{u}`. Given the target's data, the first supplies
`P`, `R`, `T` and the seven predicates for the actual `G`. The second, applied
to the original `M` and these data, supplies a special point `y` and the exact
equality for `M.integralPoints`. The constructor then gives the comparison.
The proof uses no further hypothesis.

## Scope

This module proves neither `SpecialStabilizerStatement` nor
`RootValuationBuildingConstructionStatement`. It therefore does not prove
`BuildingComparisonStatement` or maximal compactness of `M.integralPoints`.
It does not claim the full corrected ten-axiom availability package.
