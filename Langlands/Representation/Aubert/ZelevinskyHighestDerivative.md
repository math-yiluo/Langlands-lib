# A label of the highest derivative of a Zelevinsky subrepresentation

Module `Langlands.Representation.Aubert.ZelevinskyHighestDerivative`, namespace
`Langlands.Aubert.ZelevinskyHighestDerivative`.

This module proves a weak-label form of Zelevinsky 1980, Lemma 6.6, assuming the
homogeneity theorem, Zelevinsky 1980, Theorem 6.2. The surjectivity half of
`Langlands.Aubert.SegmentPolynomialComparisonStatement` (Zelevinsky 1980,
Corollary 7.5) uses it.

## Provenance

Zelevinsky 1980, 6.6, Lemma: for a multisegment `a = {Δ_1, …, Δ_r}`, the highest
derivative of `π(a) = ⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` is `π(a⁻)`, and the highest derivative
of `⟨a⟩` has a unique irreducible submodule, isomorphic to `⟨a⁻⟩`. Here `a⁻` is
the multiset `{Δ_1⁻, …, Δ_r⁻}` with empty parts dropped. Zelevinsky derives the
second part from the first one and from 6.1 (a) and 6.2.

The Lean theorem proves less than the second part of the lemma. It proves:

- the order-`λ` derivative of `π`, where `λ = ∑ i, rank Δ_i`, has an irreducible
  subrepresentation `π'`;
- `π'` is a Zelevinsky subrepresentation of a precedence-ordered product of
  segment socles whose multisegment is `a⁻`.

It does not prove uniqueness of `π'`, and it does not prove that `λ` is the
highest nonzero derivative order of `π`. Theorem 6.2 is a hypothesis `hH`, stated
as the Library proposition
`Langlands.Classification.SegmentSocleProductHomogeneity`. The first part of the
lemma for the product `d.induced` is the published Library theorem
`Langlands.Classification.segmentSocleProductHighestDerivative`. The combination
of these results, and the helper lemmas below, are internal.

## Main statement

`exists_label_subquotient F T hH ψ`: let `hH` be a proof of
`Classification.SegmentSocleProductHomogeneity.{uF, max uF uV} F T` and let `ψ`
be a unitary additive character of `F`. Let `n > 0`, let
`d : T.SegmentProductDatum.{max uF uV, uF} n` have segments `Δ_i = d.segments i`,
and let `π` be a smooth complex representation of `GL_n(F)` with
`d.IsZelevinskySubrepresentation π`: the segments are precedence-ordered (no
`Δ_i` with `i < j` precedes `Δ_j`), every block of `d` is the socle of its
segment, and `π` is an irreducible subrepresentation of `d.induced`. Write
`λ = ∑ i, (d.segments i).rank`. Then there exist

- a proof `hk : λ ≤ n`;
- a datum `d' : T.SegmentProductDatum (n - λ)`;
- a smooth representation `π'` of `GL_{n-λ}(F)`

such that

1. `d'.multisegment = d.multisegment.dropLast`, that is, the multisegment of `d'`
   is `a⁻` (`Multisegment.dropLast` from `Aubert/MultisegmentRankOrder`);
2. `d'.IsZelevinskySubrepresentation π'`;
3. `π'` is a subquotient of the order-`λ` general-linear derivative
   `(generalLinearDerivative T ψ n λ hk).obj π`. The proof produces `π'` as a
   subrepresentation.

## Helper lemmas

- `rank_le_degree`: `Δ.rank ≤ Δ.degree` for every segment, because
  `degree = length * rank` and `length ≥ 1`.
- `sum_rank_le`: for a datum of total degree `n`, `∑ i, (d.segments i).rank ≤ n`,
  by summing `rank_le_degree` and using `d.degree_sum`.
- `sum_rank_pos`: if `n > 0`, then `0 < ∑ i, (d.segments i).rank`. A datum with
  no segments has total degree `0`, and every segment has positive rank.
- `filterMap_eq_dropLastList`: the list operation written out in
  `SegmentSocleProductHighestDerivative` (keep `⟨base, length - 1⟩` when
  `2 ≤ length`, drop the segment otherwise) is the Library list truncation
  `Segment.dropLastList`. After unfolding `dropLastList`, `congr 1` closes the
  goal.
- `hasNonzeroDerivative_restriction_iff ψ hk X`: for `0 < k ≤ N + 1` and a
  representation `X` of `GL_{N+1}(F)`, the mirabolic restriction of `X` has a
  nonzero derivative of order `k` iff the general-linear derivative of order `k`
  of `X` is nontrivial. Proof: `hasNonzeroDerivative_iff` and the published
  isomorphism `generalLinearRestrictionDerivativeIso`.
- `hasFiniteLength_of_injective f hf hB`: if `f : A ⟶ B` is an injective morphism
  of smooth complex representations and `B` has finite length, then `A` has
  finite length. This is `IsFiniteLength.of_injective` applied to the module map
  `Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom f)`.

## Proof of `exists_label_subquotient`

Unpack `d.IsZelevinskySubrepresentation π` into the precedence order `ho`, the
socle hypothesis `hs`, irreducibility of `π` and an injective intertwiner
`j : π → d.induced`. Write `n = N + 1`. Then `λ ≤ N + 1` by `sum_rank_le` and
`0 < λ` by `sum_rank_pos`.

1. Highest derivative of the product. `segmentSocleProductHighestDerivative`
   with `k = λ` gives: every derivative of `d.induced` of order `j` with
   `λ < j ≤ N + 1` is zero; a datum `d'` of degree `N + 1 - λ` with segment
   socles whose segment list is the filtered list above, hence
   `Segment.dropLastList` of the list of `d` (`filterMap_eq_dropLastList`); and
   an isomorphism `e` from the order-`λ` derivative of `d.induced` to
   `d'.induced`.
2. Homogeneity. `precedenceOrdered_endpointSeparated`, with
   `cuspidalIntegralTwistFreeness`, turns `ho` into the endpoint condition of
   Theorem 6.2. Then `hH` and `isGeneralLinearHomogeneous_iff` show that the
   mirabolic restriction of `d.induced` is homogeneous.
3. Level of the product. By `level_eq_iff`, the level of the mirabolic
   restriction of `d.induced` is `λ`. The order-`λ` derivative is nonzero: by
   `hasNonzeroDerivative_restriction_iff` this is nontriviality of the order-`λ`
   general-linear derivative, which transfers along `e` to `d'.induced`, and
   `d'.induced` is nontrivial by `segmentSocleProduct_nontrivial`. Higher orders
   vanish by step 1.
4. Level of `π`. Restriction to the mirabolic subgroup is exact
   (`generalLinearRestriction_mapsShortExact`), so it preserves the injectivity
   of `j` (`LevelCalculus.map_injective_of_exact`). The restriction of `π` is
   nontrivial because `π` is irreducible. `LevelCalculus.level_eq_of_isHomogeneous`
   then gives that the restriction of `π` has the same level `λ`. By
   `level_eq_iff` and `hasNonzeroDerivative_restriction_iff`, the order-`λ`
   general-linear derivative `D π` of `π` is nontrivial.
5. Embedding of `D π`. The derivative functor `D` of order `λ` is exact
   (`generalLinearDerivativeExactness`), so `D j` is injective. Composing with
   `e` gives an injective intertwiner `D π → d'.induced`.
6. Irreducible subrepresentation. `d'.induced` has finite length
   (`SegmentProductClass.hasFiniteLength_induced`), so `D π` has finite length by
   `hasFiniteLength_of_injective`. `D π` is nontrivial (step 4), so
   `SegmentHeadSupport.exists_irreducible_subrepresentation` gives an
   irreducible `π'` with an injective `jC : π' → D π`.
7. Conclusion. Take `d'` and `π'`.
   - Multisegment: unfold `SegmentProductDatum.multisegment` and rewrite with
     `Multisegment.dropLast_coe` and the list identity from step 1.
   - Precedence order of `d'`: part (2) of `segmentInitialTruncationOrder` (with
     `cuspidalIntegralTwistFreeness`) says that `Segment.dropLastList` preserves
     precedence-ordered lists. Apply it to the list of `d` (via
     `isPrecedenceOrdered_iff_list`) and rewrite with the list identity.
   - `d'` has segment socles (step 1), `π'` is irreducible, and
     `jC ≫ D j ≫ e` is an injective intertwiner `π' → d'.induced`. So
     `d'.IsZelevinskySubrepresentation π'`.
   - `π'` is a subrepresentation, hence a subquotient, of `D π`
     (`SmoothRep.IsSubrepresentation.isSubquotient`).

## Checks

`lean_check` in a lake build of this module together with
`Aubert/SegmentProductClass` and `Aubert/SegmentPolynomialInjectivity`, on
Library `0d8048b0`, reported 0 errors and 0 warnings. `exists_label_subquotient`
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
