# The decomposition theorem for semisimple groups over a field: proof

`Langlands.GroupScheme.simpleFactorDecomposition` proves the published statement
`Langlands.GroupScheme.SimpleFactorDecompositionStatement.{u}` exactly, for an arbitrary
universe `u`, with no further hypotheses. It covers every field `k : Type u` and every group
scheme `G` over `Spec k` with `IsSemisimple G`, including the trivial group, where the index
type is empty. The statement module
[`SimpleFactorDecompositionStatement`](SimpleFactorDecompositionStatement.md)
formalizes Brian Conrad, *Reductive group schemes*, Theorem 5.1.19 (p.150). The clause
numbers below are those of its Markdown.

## Modules

The proof uses four companion modules, all in `Langlands/GroupScheme/Reductive/`:

- [`SimpleFactorPoints`](SimpleFactorPoints.md): general facts about points,
  fppf-type lifting, commutants and finite products;
- [`SimpleFactorPresentation`](SimpleFactorPresentation.md):
  `SimpleFactor.exists_almostSimplePresentation`, a central isogeny `mul : pi A ⟶ G` from a
  finite product of almost-simple groups whose factor maps are closed immersions with
  normal range;
- [`SimpleFactorCover`](SimpleFactorCover.md): the structure
  `AlmostSimpleCover G` and clause 1 for its factors;
- [`SimpleFactorSubgroups`](SimpleFactorSubgroups.md): the images `G_J` of
  subproducts and clauses 5–8.

It also imports the published
[`NormalIsogenyComplementProof`](NormalIsogenyComplementProof.md) for
`semisimpleNormalIsogenyComplement`.

## Implemented proof

Let `k` be a field and `G` semisimple. The local predicates `IsNormalSubgroup` and
`IsMinimalNormalSubgroup` of the statement are introduced as local definitions; they agree
definitionally with `SimpleFactor.IsNormalSmooth` and `SimpleFactor.IsMinimalNormalSmooth`
of `SimpleFactorCover`, so the lemmas stated with the latter close the goals directly.

1. **The cover.** `exists_almostSimplePresentation G hG` gives `I : Type u` with
   `Finite I`, almost-simple `A i`, and a central isogeny `mul : pi A ⟶ G` whose factor maps
   are closed subgroups. A central isogeny is finite (hence quasi-compact), flat and
   surjective, so these data form `D : AlmostSimpleCover G`. The proof takes
   `I := D.Index`, `A := D.factor` and `a := D.inclusion`, where
   `D.inclusion i = piFactorInclusionHom A i ≫ mul`.
2. **Clause 1.** `D.isMinimalNormalSmooth_inclusion hG`, `D.injective_range_inclusion hG`
   and `D.exists_range_eq_inclusion hG`.
3. **Clause 2.** `D.isAlmostSimple`.
4. **Clause 3.** `D.commute_inclusion`.
5. **Clause 4.** `p := mul`, with `piFactorInclusionHom A i ≫ mul = D.inclusion i` by
   definition, and `IsCentralIsogeny mul` from the presentation.
6. **`G_J`.** For every `J : Set I`, `D.exists_isSubfamilyImage hG J` gives `B J`,
   `b J : B J ⟶ G` and `fac J` with `D.IsSubfamilyImage J (b J) (fac J)` (chosen with
   `choose`). Clauses 5–7 are `isNormalSmooth` and `isSemisimple hG`;
   `range_inclusion_le` and `range_le_of_isClosedSubgroup`; and
   `exists_isMinimalNormalSmooth hG` and `exists_range_eq_of_isMinimalNormalSmooth hG`.
7. **Clause 8.** For `IsNormalSubgroup n`, the set `J := D.support n` (the factors contained
   in `n`) satisfies `range n = range (b J)` by `range_eq_of_support`. Every `J'` with
   `range n = range (b J')` equals `D.support n` by `support_eq`.
8. **Clause 9.** For `IsNormalSubgroup n`, the published `semisimpleNormalIsogenyComplement`
   gives a semisimple closed subgroup `n' : K' ⟶ G` with normal range, commuting with `n`,
   and with central-isogeny multiplication `commutingSubgroupMultiplicationHom n n' hc`.
   Since `K'` is semisimple, it is smooth and connected, so `IsNormalSubgroup n'`. For
   uniqueness, let `n''` be another such subgroup. By `D.mem_support_complement_iff`, both
   `D.support n''` and `D.support n'` are the complement of `D.support n`, so they are
   equal. Then `range_eq_of_support` for the subfamily image on `D.support n''` gives
   `range n'' = range (b (D.support n'')) = range n'`.

## Relation to Conrad's proof

Conrad proves Theorem 5.1.19 by passing to a separable closure, applying the split case
(Proposition 5.1.17, via root systems) and descending. The Lean proof does not use roots,
separable closures or Galois descent. The presentation of `SimpleFactorPresentation` is built by induction on
dimension from the published complement theorem `semisimpleNormalIsogenyComplement`. The
identification of the minimal normal subgroups, the subgroups `G_J` and the uniqueness
statements are then proved over `k` from the published dichotomy for almost-simple normal
subgroups (`IsAlmostSimple.range_le_or_commute_of_normal`), perfectness of semisimple groups
(`semisimplePerfect`), semisimplicity of smooth connected normal subgroups
(`IsSemisimple.of_normalSubgroup`), the published image construction
`HomImage.exists_image`, and fppf-type lifting along flat surjective homomorphisms.

## Axioms

An axiom check reports that the theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`.
