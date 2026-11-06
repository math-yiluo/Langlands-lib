# Topology on adelic-level points of algebraic spaces

Author: Worker 105.

This module defines the topology on the adelic-level points of an algebraic space over
the `S`-integers of a global field. Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), uses this topology on printed p.17. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module also
defines the change-of-level map for algebraic spaces. It makes definitions only and
proves nothing about them beyond the defining inducing property.

Conrad writes on printed p.17: "for a separated algebraic space `X_S` of finite type
over `O_{F,S}`, the product topology on `X_S(A_{F,S})` via Proposition 5.2 and
Proposition 5.4 is locally compact Hausdorff and induces an open embedding
`X_{S'}(A_{F,S'}) → X_{S''}(A_{F,S''})` where `X_{S'}` and `X_{S''}` are as in
Theorem 3.6." Proposition 5.2 (printed p.13) says that the map (3.6.1),
`X_S(A_{F,S}) → ∏_{v∈S} X_v(F_v) × ∏_{v∉S} X_{S,v}(O_v)`, is bijective.
Proposition 5.4 (printed p.14) topologizes the rational points of an algebraic space
over a henselian valued field. In Theorem 3.6 (printed p.6), `X_{S'}` is the base change
of `X_S` to `O_{F,S'}` for `S ⊆ S'`.

## Generic constructions

These are in namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`. Let `C` be a
commutative ring and `X : AlgebraicSpace (Spec (CommRingCat.of C))` an actual algebraic
space over `Spec C`. `RingPoints C X A` is the set of `A`-valued points of `X` over `C`
(from `Langlands/AlgebraicGeometry/AlgebraicSpace/RingPoints.lean`).

- `fieldValuedPointMap C X φ`, for a `C`-algebra map `φ : A →ₐ[C] L` to a field `L`, is
  the map `X(A) → X_L(L)`. It sends `p` to `RingPoints.changeRing φ p`, viewed as an
  `L`-point of the base change `baseChange (Spec.algebraMap C L) X` through the inverse
  of the published equivalence `baseChangeRingPointsEquiv C L L X`.
- `fieldValuedPointTopology C X φ`, for a topology on `L`, is the topology on `X(A)`
  induced along `fieldValuedPointMap C X φ` from `etaleChartTopology` on the rational
  points of the base change of `X` to `Spec L`. `etaleChartTopology` is the published
  topology of Conrad's proof of Proposition 5.4
  (`Langlands/AlgebraicGeometry/AlgebraicSpace/EtaleChartTopology.lean`).
  `fieldValuedPointMap_isInducing` records the defining identity.
- `coordinatePointMap C X R π`, for a family of `C`-algebra maps `π i : A →ₐ[C] R i`,
  is the map `X(A) → ∏ᵢ X(R i)` sending `p` to `i ↦ RingPoints.changeRing (π i) p`.
- `coordinateProductTopology C X R L φ`, for a family of `C`-algebra maps
  `φ i : R i →ₐ[C] L i` to topological fields, is the product over `i` of the topologies
  `fieldValuedPointTopology C X (φ i)`.
- `coordinatePointTopology C X R L φ π` is the topology on `X(A)` induced along
  `coordinatePointMap C X R π` from `coordinateProductTopology C X R L φ`.
  `coordinatePointMap_isInducing` records the defining identity.

## The arithmetic level topologies

These are in namespace `Langlands.Global`. The level rings, their factor families,
the coordinate projections `...LevelFactorAlgHom`, the `S`-integer rings and their
inclusions are the published ones from `Langlands/Global/AdelicLevelModelPoints.lean`
and `Langlands/Global/AdelicLevelModelTransition.lean`.

- `CurvePlaceLevelField k F S i` is the completion `curvePlaceCompletion v` at the
  place `v` of the factor `i`, for `i` in `S` and outside `S`.
  `curvePlaceLevelFieldInclusion` is the identity at places in `S`, and the inclusion
  of the completed valuation ring `curvePlaceCompletionIntegers v` in the completion at
  places outside `S`. `curvePlaceLevelFieldAlgHom` is this inclusion as a map of
  algebras over `curvePlaceSIntegers k F S`, where the `S`-integers act on the completed
  field through the factor (instance `instAdelicSpaceLevelTopology3`).
- `NumberFieldLevelField K S i` is the completion at the place of the factor `i`:
  `InfiniteCompletion K v` at an infinite place, and `FiniteCompletion K v` at a finite
  place in `S` and outside `S`. `numberFieldLevelFieldInclusion` is the identity at
  infinite places and at finite places in `S`, and the inclusion of
  `v.adicCompletionIntegers K` in the completion at finite places outside `S`.
  `numberFieldLevelFieldAlgHom` is this inclusion as a map of algebras over Mathlib's
  ring of `S`-integers `(S : Set (FinitePlace K)).integer K`.
- `curvePlaceSpaceLevelTopology k F S X` and `numberFieldSpaceLevelTopology K S X` are
  the topologies on `RingPoints O X (level ring)` for an algebraic space `X` over
  `Spec O`, with `O` the `S`-integers. They are `coordinatePointTopology` for the
  coordinate projections of the level ring and the inclusions of the factors in their
  completed fields.

Thus the topology is induced along the map (3.6.1) from a product topology. At a
factor `F_v` the topology on `X(F_v)` is Conrad's topology from Proposition 5.4 on
`X_v(F_v)`, through the identification of `F_v`-points of `X` with rational points of
the base change. At a factor `O_v` the topology on `X(O_v)` is induced from the
`F_v`-points along the inclusion `O_v → F_v`.

## Change of level

Let `S ⊆ T` with inclusion proof `hST`.

- `curvePlaceSpaceLevelBaseChange k F hST X` and `numberFieldSpaceLevelBaseChange K hST X`
  are the base change of `X` (published `baseChange` from
  `Langlands/AlgebraicGeometry/AlgebraicSpace/SpaceBaseChange.lean`) along the spectrum
  of the inclusion of the `S`-integers in the `T`-integers (`curvePlaceSIntegersMap`,
  `numberFieldSIntegersMap`). This is Conrad's `X_T`.
- `curvePlaceSpaceLevelTestMap k F hST` and `numberFieldSpaceLevelTestMap K hST` are the
  spectrum of the level inclusion `A_{F,S} → A_{F,T}` (`curvePlaceAdeleLevelMap`,
  `numberFieldAdeleLevelMap`), as a morphism over `Spec O_S` from the spectrum of the
  `T`-level, viewed over `Spec O_S` through `Over.map`, to the spectrum of the `S`-level.
  The structure-map compatibility comes from the published
  `...AdeleLevelDiagonal_natural` identities.
- `curvePlaceSpaceLevelTransition k F hST X` and
  `numberFieldSpaceLevelTransition K hST X` are the maps
  `X(A_{F,S}) → X_T(A_{F,T})`. They pull an `A_{F,S}`-point back along the test map
  with `X.pullback`. The result is read as an `A_{F,T}`-point of the base change `X_T`.
  This uses the definitional form of points of a base change in `SpaceBaseChange`.

## Relation to the source and derived content

Conrad defines the topology on `X_S(A_{F,S})` by transporting the product topology
through the bijection of Proposition 5.2. That bijection needs `X_S` separated and of
finite type (`AdelicSpaceLevelPointsStatement`, not proved here). The module instead
induces the product topology along the map (3.6.1), which is defined for every algebraic
space. When (3.6.1) is bijective, the induced topology is the transported topology.
Inducing the topology first, without geometric hypotheses, is an implementation choice.
The definitions make no claim that (3.6.1) is bijective.

Conrad does not say how `X_{S,v}(O_v)` is topologized. The module uses the topology
induced from `X(F_v)` along `O_v → F_v`, where `X(F_v)` carries the topology of
Proposition 5.4. This is the topology Corollary 5.7 (printed p.16) refers to when it
says that the subset `X(R)` of `X(k)` is open and closed. Conrad's p.17 sentence calls
this "an application of Corollary 5.7". This reading is derived. For a non-separated
`X`, the map `X(O_v) → X(F_v)` need not be injective, and the topology is still the
induced one.

The definitions allow any fields `k` and `F` with `[Algebra k F]`, any finite set of
places `S` (possibly empty), and any number field `K`. They do not assume that `X` is
separated or of finite type, and they do not assume that `k` is finite. For a number
field, `S` ranges over finite places and every infinite place is a factor, as in the
published level rings. Also derived here: the names, the generic coordinate
constructions, the completed-field families and their inclusion maps, and the
formulation of the change of level through `X.pullback` and `Over.map`.

## Not stated here

Local compactness, the Hausdorff property, the open-embedding property of the change of
level, the comparison with the scheme-case topology
(`Langlands/Global/AdelicLevelModelTopology.lean`) for separated schemes, and the
topology on `X(A_F)` through the colimit over levels are separate statements. Continuity
of the change of level and its compatibility with the coordinate maps are not proved
here.
