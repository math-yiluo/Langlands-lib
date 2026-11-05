# Conditional assembly of archimedean local parabolic Iwasawa existence

Author: Worker 1359.

This internal derived module reduces the exact archimedean target
`Langlands.Global.InfinitePlaceGroupPoints.ParabolicIwasawaStatement` to two
structural propositions, which remain explicit hypotheses:

* `Langlands.GroupScheme.ConnectedReductiveSelfAdjointRealizationStatement`
  (statement candidate `549ae55b-089a-4dad-97b4-8ffee22137ff`, included
  unchanged): every connected reductive group over a field with an `RCLike`
  structure has a closed matrix representation whose full rational-point
  matrix range is stable under conjugate transpose;
* `Langlands.GroupScheme.ParabolicDynamicStatement` (Milne, Theorem 25.1, as
  stated in `Absolute/BorelStatement`): over any field, a closed subgroup of a
  connected reductive group is parabolic if and only if its range is the
  dynamic parabolic subgroup functor of a cocharacter defined over that field.

The module has three layers, all taking the two hypotheses `hR` and `hD`:

* `exists_iwasawa_of_realization_of_dynamic hR hD F G hG P p hp v` proves, for
  one number field, group, parabolic subgroup and infinite place, the
  existence of a compact subgroup of the actual completion-point group,
  maximal among all compact subgroups, whose product with the literal point
  range of `p` is the whole group;
* `iwasawaCompact hR hD F G hG P p hp v` is the subgroup chosen from that
  existence statement (by `Classical.choose`), and `iwasawaCompact_spec` states
  its three properties: compactness, maximality among compact subgroups, and
  `Set.range (P.affinePointsTarget p _) * iwasawaCompact .. = Set.univ`;
* `parabolicIwasawaStatement_of_realization_of_dynamic hR hD` packages these
  into the exact target at the same arbitrary universe `u`.

The chosen subgroup is not canonical: it depends on the representation
supplied by `hR`, and only the three listed properties are asserted. The
module therefore does not prove the target unconditionally. Neither
hypothesis is weakened, specialized to split or anisotropic groups, or
restricted to one component of the real points.

## Proof

The proof of `exists_iwasawa_of_realization_of_dynamic` runs as follows. Fix
a number field `F : Type u`, a connected reductive group `G` over `F`, a
parabolic subgroup `p : P ⟶ G`, and an infinite place `v`. Affineness of the
underlying scheme of `G` follows from the reductivity predicate.

1. The target is unfolded to `CompactIwasawa.HasDecomposition` for the actual
   completion-valued point map of `p`. The published
   `hasDecomposition_completionBaseChange_iff` (in
   `InfinitePlaceIwasawaBaseChange`) rewrites it to the same decomposition for
   the rational points of the actual pullbacks of `G` and `P` to
   `v.Completion`. The comparison is a homeomorphism of the evaluation
   topologies, so compactness, maximality and the literal range covering are
   unchanged.
2. `completion_isRCLikeNormedField` (in `InfiniteCompletionRCLike`) shows the
   completion is an `IsRCLikeNormedField`, and `IsRCLikeNormedField.rclike`
   supplies an `RCLike` structure extending the completion's existing normed
   field structure. The topology on the completion, and therefore the
   evaluation topology on the points, is the one in the target.
3. `isConnectedReductive_completionBaseChange` and
   `isParabolicSubgroup_completionBaseChange` show that the pulled-back group
   is connected reductive and the pulled-back homomorphism is parabolic.
4. Hypothesis `hR`, applied to the completion and the pulled-back group, gives
   a closed matrix representation `ρ` with conjugate-transpose-stable
   rational-point range.
5. The parabolic subgroup is a closed subgroup, so its morphism of schemes
   over the base is a monomorphism (`Over.mono_of_mono_left`). Hypothesis `hD`
   over the completion then gives a cocharacter `χ` with
   `SubgroupFunctor.range p = Dynamic.parabolic χ`; with the monomorphism this
   is exactly `(Dynamic.parabolic χ).IsRepresentedBy p`.
6. The published `MatrixRepresentation.affineDynamicIwasawa` (in
   `AffinePolarIwasawa`), applied to `ρ` with `S = v.Completion`, gives one
   compact subgroup, maximal among all compact subgroups, whose product with
   the literal point range of every representative of every dynamic parabolic
   is the whole point group. Specializing to `χ` and `p` gives the three
   required conclusions.

`iwasawaCompact` and `iwasawaCompact_spec` are `Classical.choose` and
`Classical.choose_spec` of this existence theorem, and the final theorem
introduces the quantified data and returns the chosen subgroup with its
specification.

## Provenance

The reduction is an internal assembly of published Library constructions;
it makes no new literature claim. The two hypotheses are unproved
proposition definitions. Proofs of them are separate work; the final proof of
the target applies this theorem to those proofs.
