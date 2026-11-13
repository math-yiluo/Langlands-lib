# The local rank-one classification from actual Tits indices

Author: Worker 5442.

This module contains one definition and three theorems.

## `IsSimplyConnected.locallyOfFiniteType`

For a field `K` and a group scheme `G` over `Spec K`,
`IsSimplyConnected G` implies `LocallyOfFiniteType G.X.hom`.

Proof: `IsSimplyConnected G` contains `IsSemisimple G`, which contains
`IsConnectedReductive G`, whose `smooth` field gives
`Smooth G.X.hom`; a smooth morphism is locally of finite presentation,
hence locally of finite type, by instance search.

This is used because the actual-index statements below take the
instance `[LocallyOfFiniteType G.X.hom]`, while
`LocalRankOneClassificationStatement` does not assume it.

## `LocalRankOneClassificationIndexInputs`

`Langlands.GroupScheme.LocalRankOneClassificationIndexInputs.{u}` is the
`Prop`-valued conjunction, in this order, of the seven published,
unproved propositions listed below as hypotheses 1–7, all at universe
`u`. It asserts nothing beyond them; it only bundles the remaining
inputs of the classification in one declaration.

## `localRankOneClassification_of_indexStatements`

`Langlands.GroupScheme.localRankOneClassification_of_indexStatements`
proves `LocalRankOneClassificationStatement.{u}` from seven explicit
hypotheses, each a published, unproved Library proposition at the same
universe `u`:

1. `TitsIndexExistenceStatement` — every semisimple affine locally
   finite type group over a field has actual Tits-index data
   `d : TitsIndexData G`;
2. `LocalRankOneTitsIndexStatement` — over a nonarchimedean local field,
   the actual index of an absolutely almost-simple simply connected
   group of split rank one is one of `¹A_(2d−1),1^(d)`, `²A_2,1^(1)` or
   `²A_3,1^(1)`, `C_2,1^(2)` or `C_3,1^(2)`, `²D_4,1^(2)`, `¹D_5,1^(2)`;
3. `InnerTypeANormOneStatement` and
4. `CentralSimpleUnits.MatrixNormOneSplitRankStatement` — consumed by
   the published conditional theorem `exists_binary_model_of_innerTypeA`;
5. `OuterTypeARankOneHermitianStatement` — outer type `A` indices give
   special unitary Hermitian models;
6. `TypeCRankOneQuaternionicStatement` — type `C` indices give
   quaternionic symplectic models;
7. `TypeDRankOneSpinStatement` — the two type `D` indices give spin
   covers of quaternionic `σ`-quadratic forms (new statement in
   `TypeDRankOneSpinStatement.lean`).

The theorem does not prove any of these hypotheses. It uses none of
`LocalAbsolutelyAlmostSimpleRankOneKneserTitsStatement`,
`LocalRankOneKneserTitsStatement` or `LocalKneserTitsStatement`, which
are consequences of the classification in the published route.

### Implemented proof

Fix a nonarchimedean local field `K`, an affine group scheme `G` over
`Spec K`, and `hsc : IsSimplyConnected G`, `habs :
IsAbsolutelyAlmostSimple G`, `hG : splitRank G = 1`.

1. Obtain `LocallyOfFiniteType G.X.hom` from
   `IsSimplyConnected.locallyOfFiniteType`.
2. Apply hypothesis 1 to `hsc.isSemisimple` to obtain actual index data
   `d`.
3. Apply hypothesis 2 and split into its five alternatives.
   - Inner type `A` with degree `degree`: convert the index to
     `d.HasInnerTypeA (2 * degree − 1)` by the published
     `HasRankOneInnerAIndex.hasInnerTypeA`, and apply
     `exists_binary_model_of_innerTypeA` with hypotheses 3 and 4. Its
     conclusion is family (i) verbatim.
   - Outer type `A` with absolute rank `n`: hypothesis 5 gives a
     quadratic separable extension `L`, a diagonal Hermitian form
     `H` on `Fin (n − 1)` with unit weights `w`, `H.IsAnisotropic` and an
     isomorphism with `HermitianRoot.SchemeModel.groupScheme K L H w hw`.
     Since the index forces `n = 2` or `n = 3`, `n − 1 = 1` or `2`; this
     is family (ii) with `m = n − 1`.
   - Type `C` with rank `n`: hypothesis 6 gives the quaternion algebra,
     the involution, `NeZero n` and an antihermitian invertible `H` of
     Witt index 1 with `G ≅ σ.symplecticGroup H`; the index supplies
     `n = 2 ∨ n = 3`. This is the symplectic disjunct of family (iii).
   - `²D_4,1^(2)` and `¹D_5,1^(2)`: hypothesis 7 with `n = 4`,
     respectively `n = 5`, gives the quaternion algebra, the involution,
     the nondegenerate `σ`-quadratic form of Witt index 1 and the spin
     cover. This is the spin disjunct of family (iii) with `m = 4`,
     respectively `m = 5`.

All witnesses are passed through unchanged; only the arithmetic fact
`n − 1 ∈ {1, 2}` is computed.

## `localRankOneClassification_of_indexInputs`

`localRankOneClassification_of_indexInputs` takes
`h : LocalRankOneClassificationIndexInputs.{u}` and proves
`LocalRankOneClassificationStatement.{u}`. It destructures `h` into its
seven components and applies
`localRankOneClassification_of_indexStatements`.

## Provenance

Internal. The definition bundles published propositions, and the theorems compose published Library propositions and the
published conditional theorem `exists_binary_model_of_innerTypeA`; it
formalizes no new assertion from the literature. The family-by-family
case split follows the list of Prasad–Raghunathan, *On the Kneser–Tits
problem* (1985), §2, printed p.111 / PDF p.6, and the Tits indices
recorded in `LocalRankOneClassificationStatement.md`.

The unconditional `LocalRankOneClassificationStatement` still needs
proofs of all seven hypotheses; the closing theorem is this reduction
applied to them.
