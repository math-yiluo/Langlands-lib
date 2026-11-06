# Rational points over a henselian field and over its completion

Author: Worker 105.

`HenselianCompletionPointEmbeddingStatement` states part (2) of Proposition 5.11 of
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.18. The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module
only states the result and contains no proof.

Conrad's Proposition 5.11 (printed p.18) begins: "Let `k′/k` be an extension of
henselian valued fields, and `X` a (quasi-separated) algebraic space locally of finite
type over `k`." Part (2) reads: "The natural map `X(k) → X(k̂) = X_{k̂}(k̂)` is a
topological embedding." Part (2) involves only `k`, its completion `k̂` and `X`.

## Objects

Throughout, `K : Type u` is a nontrivially normed field. The algebraic spaces are the
Library's actual algebraic spaces `X : AlgebraicSpace (Spec (CommRingCat.of K))` from
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`. The statement uses only
published definitions.

- `IsHenselianValuedField K` (from
  `Langlands/AlgebraicGeometry/PointTopology/HenselianEtalePointStatement.lean`) says
  that the norm of `K` extends uniquely to an absolute value on every algebraic
  extension field. This is Conrad's definition of a henselian valued field (printed
  p.14).
- `IsQuasiSeparatedLocallyFiniteType K X` (from
  `Langlands/AlgebraicGeometry/AlgebraicSpace/HenselianSpacePointTopologyStatement.lean`)
  says that `X` is quasi-separated and locally of finite type over `Spec K`. These are
  the spaces of Proposition 5.11.
- `UniformSpace.Completion K` is Mathlib's completion `K̂` of `K` for the uniform
  structure of its norm. Mathlib makes it a field (and a normed field), with the
  completion topology, and a `K`-algebra whose structure map is the canonical inclusion
  `K → K̂`. `Algebra.ofId K (UniformSpace.Completion K)` is this inclusion as a
  `K`-algebra map.
- `RingPoints K X A` (from `RingPoints.lean`) is the set `X(A)` of `A`-valued points of
  `X`, for a `K`-algebra `A`. `RingPoints.changeRing φ` is the map `X(A) → X(B)` induced
  by a `K`-algebra map `φ : A → B`, by pulling back along the actual morphism
  `Spec B ⟶ Spec A`.
- `baseChange (Spec.algebraMap K (UniformSpace.Completion K)) X` (from
  `SpaceBaseChange.lean`) is the base change `X_{K̂}` of `X` along
  `Spec K̂ ⟶ Spec K`, an actual algebraic space over `Spec K̂`.
  `baseChangeRingPointsEquiv K K̂ K̂ X` is the Library's identification
  `X_{K̂}(K̂) ≃ X(K̂)` of the rational points of the base change with the `K̂`-valued
  points of `X`.
- `etaleChartTopology F Y` (from `EtaleChartTopology.lean`), for a topological field
  `F` and an algebraic space `Y` over `Spec F`, is the strongest topology on `Y(F)`
  making every map `U(F) → Y(F)` continuous, for étale maps `U → Y` from actual schemes
  of finite type over `F`, where `U(F)` has the scheme point topology. This is the
  topology that Conrad constructs in the proof of Proposition 5.4. It is used over `K`
  and over `K̂`.

## The statement

`HenselianCompletionPointEmbeddingStatement` says: for every nontrivially normed field
`K : Type u` with `IsHenselianValuedField K` and every algebraic space `X` over
`Spec K` with `IsQuasiSeparatedLocallyFiniteType K X`, the map

`x ↦ (baseChangeRingPointsEquiv K K̂ K̂ X).symm (RingPoints.changeRing (Algebra.ofId K K̂) x)`

from `RingPoints K X K` to `RingPoints K̂ X_{K̂} K̂` is a topological embedding
(`Topology.IsEmbedding`), where the source carries `etaleChartTopology K X` and the
target carries `etaleChartTopology K̂ X_{K̂}`.

## Relation to the source and derived content

Conrad's "natural map `X(k) → X(k̂) = X_{k̂}(k̂)`" is the composite in the statement: a
rational point is first viewed as a `k̂`-valued point along `k → k̂`, and the equality
`X(k̂) = X_{k̂}(k̂)` is the Library's base change identification of points.

Conrad's topologies on `X(k)` and `X_{k̂}(k̂)` are those of his Proposition 5.4, for the
henselian fields `k` and `k̂` (the completion is complete, hence henselian). The
statement uses the étale-chart topology over both fields instead. Conrad's existence
proof of Proposition 5.4 (printed p.15) asserts that this topology "does the job", that
is, it has all the properties of Proposition 5.4. That claim is stated separately
as `EtaleChartTopologyAdmissibleStatement`; with it and the uniqueness
part of Proposition 5.4, the étale-chart topology is the topology of Proposition 5.4 on
quasi-separated spaces locally of finite type. The base change `X_{k̂}` is again
quasi-separated and locally of finite type over `k̂`
(`IsQuasiSeparated.baseChange` and `HasAtlasProperty.baseChange` in
`SpaceBaseChange.lean`). Using the concrete topology avoids quantifying over all
admissible families and keeps the statement about the actual point spaces.

Quasi-separatedness is Conrad's standing convention for Section 5 (printed p.13). The
completion is Mathlib's completion of the norm uniformity, which is the completion of
the valued field `k` in Conrad's sense. Also derived here: the name of the statement.

## Not stated here

- Part (1) of Proposition 5.11, on Weil restriction along a finite extension `k′/k` of
  henselian valued fields, needs the Weil restriction of algebraic spaces from
  Conrad's Lemma 5.10 and is not part of this statement.
- Part (3), the embedding `X(k) → X_{k′}(k′)` for spaces covered by separated
  Zariski-open subsets (a closed embedding when `k` is closed in `k′`), is not part of
  this statement.
- Conrad's proof of (2) (printed p.19) uses an étale cover `U → X` by a separated
  scheme with `U(k) → X(k)` surjective and the fact that étale `k`-schemes have all
  `k̂`-points rational because `k` is henselian. These are proof material.
