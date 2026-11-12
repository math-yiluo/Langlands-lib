# Adelic points of separated algebraic spaces over global fields

Authors: Worker 208, Worker 105.

This module proves `Langlands.Global.AdelicSpacePointTopologyStatement`, the
claims of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(31 December 2011), printed p.17, on adelic points of separated algebraic
spaces of finite type over global fields of both characteristics. The source
is registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

## Declaration

- `Langlands.Global.adelicSpacePointTopology :
  AdelicSpacePointTopologyStatement.{u}`, for an arbitrary universe `u`.

## Proof

The proof is one application of Worker 105's
`AdelicSpacePointTopologyProof.adelicSpacePointTopology_of_spread`, which
derives the statement from three inputs. The theorem supplies them as
follows.

- The filtered colimit comparison for points of algebraic spaces,
  `Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredRingPointComparison`
  (Conrad's Theorem 3.4 for algebraic spaces, points part). It is supplied by
  `spaceFilteredRingPointComparison` from the module
  `Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredRingPointProof`.
- The function-field spread clause `CurvePlaceSpaceSpreadStatement`, supplied
  by `AdelicSpaceSpreadIndependenceProof.curvePlaceSpaceSpread`.
- The number-field spread clause `NumberFieldSpaceSpreadStatement`, supplied
  by `AdelicSpaceSpreadIndependenceProof.numberFieldSpaceSpread`.

The other clauses of the statement (Points, Maps and Scheme, for both kinds of
global field) are proved inside `adelicSpacePointTopology_of_spread` from the
colimit comparison; see `AdelicSpacePointTopologyProof.md`. The spread clauses
combine the existence of separated models of finite type over rings of
`S`-integers (`AdelicSpaceSpreadExistenceProof`, from the model existence
theorem `spaceLimitModelExistence`) with the independence of the adelic
topology from the model (`AdelicSpaceSpreadIndependenceProof`, from the
morphism descent theorem `spaceLimitMorphismDescent` and Worker 105's
enlargement lemma `AdelicSpaceSpreadInitialSet`).

## Scope

The theorem proves the published statement as it stands, for separated
algebraic spaces of finite type over rings of `S`-integers in both
characteristics. It adds no hypothesis beyond those of the statement.
