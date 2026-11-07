# Adelic-level points of separated finite type algebraic spaces

Author: Worker 105. Submission preparation and source/dependency verification: Worker 1568.

The Lean proof is reused from Worker 105's shared draft for this task. Worker 1568 clarified
the distinction between the finite free descent used here and Conrad's cyclic étale cover,
without changing the mathematical proof.

Proof of `Langlands.Global.AdelicSpaceLevelPointsStatement.{u}`, Proposition 5.2 of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
pp.13–14, for global fields of both characteristics. The entry theorem is
`adelicSpaceLevelPoints`; its components are `numberFieldSpaceLevelPoints` and
`curvePlaceSpaceLevelPoints`.

The target says: for a separated algebraic space `X` of finite type over the `S`-integers of
a number field (resp. a global function field with `S` nonempty), restriction to the local
factors `X(A(F,S)) → ∏ X(factor)` is bijective. The factors are the completions at the
infinite places and at the places of `S`, and the completed valuation rings away from `S`.

## Route

The adelic level ring is isomorphic, as an algebra over the `S`-integers, to the product of
its local factors (the Library's `numberFieldLevelFactorAlgEquiv` and
`curvePlaceLevelFactorAlgEquiv`). The factor projections `numberFieldLevelFactorAlgHom` and
`curvePlaceLevelFactorAlgHom` are the coordinate projections composed with this isomorphism.
Every factor is a complete local ring. So the restriction map is the composite of change of
coefficients along the isomorphism, which is bijective, and the product map of
`SpaceProductPoints.separatedProductPoints_bijective`.

In the general product theorem, the local lifts have finite free algebras of one positive
rank. The tensor-square comparison and separatedness identify the descent datum, and the
fppf sheaf condition descends the assembled point. Conrad instead uses cyclic unramified
extensions over the local integer rings and étale descent; no cyclic action or étaleness of
the product cover is asserted or needed by this implementation. Completeness of a factor
here means completeness for its maximal ideal, so fields use the zero ideal.

## Declarations

Namespace `Langlands.Global.AdelicSpaceLevelPointsProof`:

- `isAdicComplete_field`: a field is complete for its maximal ideal `⊥`.
- `isAdicComplete_adicCompletionIntegers`: the completed integers at a height-one prime of a
  Dedekind domain are complete for their maximal ideal. This is the Library's
  `rankOneDiscreteValuationSubring_isAdicComplete`.
- `changeRing_bijective`: change of coefficients along an algebra isomorphism is bijective,
  with inverse change along the inverse (`ringTestMap_id`).
- Instances: every factor `NumberFieldLevelFactor K S i` and `CurvePlaceLevelFactor k F S i` is
  complete for its maximal ideal. Infinite and finite completions are fields; the factors away
  from `S` are completed integer rings.

Namespace `Langlands.Global`:

- `numberFieldSpaceLevelPoints : NumberFieldSpaceLevelPointsStatement.{u}`.
- `curvePlaceSpaceLevelPoints : CurvePlaceSpaceLevelPointsStatement.{u}`. The nonemptiness of
  `S` is not used.
- `adelicSpaceLevelPoints : AdelicSpaceLevelPointsStatement.{u}`.

## Modules

The proof uses the helper modules `ProductPointsDescent` (pure algebra), `ProductPointsGluing`,
`UnramifiedHenselExtension`, `ProductPointsLocalLift` and `SpaceProductPointsSurjective`, all in
`Langlands/AlgebraicGeometry/AlgebraicSpace` and described in their Markdown. It also uses
`EtaleChartFibreCount` and `EtaleAlgHomCount`, the fibre bound for étale charts from the Cor 5.7
compactness proof. The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Proposition 5.2 and its
  proof, printed pp.13–14.
