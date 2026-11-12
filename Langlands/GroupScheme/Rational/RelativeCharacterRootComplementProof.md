# Proof of the intrinsic character/root complements

Author: Worker 3891.

`relativeCharacterRootComplement` proves the published proposition
`RelativeCharacterRootComplementStatement.{u}` exactly, at arbitrary universe `u`.
Its type is that proposition, with no added hypothesis. Fix any field `k`, any
connected reductive group scheme `G` over `k` and any actual maximal split torus
`i : T.toGrp ⟶ G`. Then `relativeRootSpan i` and the range of
`rationalCharacterRestrictRat i` are complementary in `ℚ ⊗[ℤ] characterLattice T`.
In the published real space `RealTorusSpace.Vstar T`, `relativeRootSpanReal i` and
the range of `rationalCharacterRestrictReal i` are complementary. All actual
relative roots are kept, including multipliable roots. Split rank zero and the
empty root set are included.

## Implemented proof

The proof has four steps.

1. **A linear-algebra lemma.** `Langlands.LinearAlgebra.eq_zero_of_fixed_of_mem_span_negated`
   concerns a finite group `W` acting `ℚ`-linearly on `V` through `ρ`, and a set
   `R ⊆ V` with the following property: every `r ∈ R` satisfies `ρ w r = -r` for
   some `w`. The lemma says that a vector in the span of `R` that is fixed by
   every `ρ w` is zero. The proof uses the sum `S = ∑ w, ρ w`, which satisfies
   `S (ρ s v) = S v` after reindexing the sum. For `r ∈ R` with `ρ s r = -r` this
   gives `S r = -S r`, so `S r = 0`. Hence `S` vanishes on the span of `R`.
   For a fixed vector `x` we have `S x = (card W) • x`. So `x = 0`, because
   `card W ≠ 0` in `ℚ`.

2. **Restricted characters are Weyl-fixed.** The published
   `relativeWeylFullRatAction_restrictionRange` says that the full rational
   action `relativeWeylFullRatAction i` of the actual quotient
   `relativeWeylGroup i = N(k)/Z(k)` fixes every vector
   `rationalCharacterRestrictRat i y`. Its proof reduces to the published
   `weylAction_torusCharacterRestrict`: conjugation by a normalizing rational
   point fixes every rational character of `G`.

3. **Every root is negated by a normalizer point.**
   `IsConnectedReductive.exists_weylAction_eq_neg` takes each actual relative
   root `α`. The published `RelativeRoot.exists_rootPoint_actual` gives a
   nonidentity rational point `x` of the actual root subgroup. The published
   theorem `rootRankOneFactorization` (relative-root rank-one factorization) gives
   an opposite factor pair `p` for `x`. Then the published
   `RelativeRoot.IsOppositeFactorPair.weylAction_eq_neg` says that the
   normalizing point `p.1 * x * p.2` sends `α` to `-α` under `weylAction i`.

4. **Assembly.** In `IsConnectedReductive.relativeRootSpan_disjoint_restrictionRange`,
   take `x` in both subspaces. The published
   `IsConnectedReductive.finite_relativeWeylGroup` makes the quotient finite.
   Apply step 1 with `ρ = relativeWeylFullRatAction i` and `R` the image of the
   actual relative roots in `ℚ ⊗[ℤ] characterLattice T`. Step 3 supplies the
   negating elements, using `relativeWeylFullRatAction_mk` and `ratAut_toRat`.
   Step 2 shows that `x` is fixed. Hence `x = 0`.

   The published `IsConnectedReductive.relativeRootSpan_sup_restrictionRange_eq_top`
   proves that the two subspaces span. With disjointness this gives
   `IsConnectedReductive.relativeRootSpan_isCompl_restrictionRange`. The published
   `relativeCharacterRootComplementReal_of_rat` converts the rational complement
   into the real complement. Together these give `relativeCharacterRootComplement`.

## Dependencies and independence

The proof uses the following published theorems:

- spanning, `IsConnectedReductive.relativeRootSpan_sup_restrictionRange_eq_top`;
- real scalar extension, `relativeCharacterRootComplementReal_of_rat`;
- finiteness of the quotient, `IsConnectedReductive.finite_relativeWeylGroup`;
- `rootRankOneFactorization`;
- `RelativeRoot.exists_rootPoint_actual`;
- `RelativeRoot.IsOppositeFactorPair.weylAction_eq_neg`;
- `relativeWeylFullRatAction_restrictionRange`.

The spanning theorem depends on the root-annihilator centrality theorem, split
components and finite-index restriction to a split component.

The finiteness theorem depends on faithfulness of the action on the root span,
and that faithfulness is proved from joint spanning. The chain in the Library is:

1. `relativeRootsRestrictedCharactersSpan` (joint spanning by the actual roots
   and the restricted characters), proved from the same spanning theorem
   `IsConnectedReductive.relativeRootSpan_sup_restrictionRange_eq_top`;
2. `IsSplitTorus.relativeWeylAction_injective_of_span`: joint spanning makes
   the action `relativeWeylAction i` of the quotient on `relativeRootSpan i`
   injective;
3. `IsSplitTorus.finite_relativeWeylGroup_of_span`: this injectivity makes the
   quotient finite, through `IsSplitTorus.finite_relativeWeylGroup_of_action_injective`,
   because the image of the action is finite by finiteness of the root set;
4. `IsConnectedReductive.finite_relativeWeylGroup`, which applies item 3 to the
   spanning of item 1.

None of these theorems assumes the complement being proved, a root-system
realization or `RelativeRootSystemStatement`. So the proof uses root-span
faithfulness only through this independently proved finiteness.

The proof does not use `RelativeRootSystemStatement`, `HasRelativeRootSystem`
or any root-system realization. It does not use generation of the relative Weyl
group. From the rank-one theorem it uses only one consequence: each relative root
is negated by some normalizing rational point. It does not use
`CentralSplitTorusCharacterStatement`, `CharacterRestrictionStatement` or any
injectivity of character restriction. No complement, rank or realization
conclusion appears as a hypothesis, and the Library theorem
`IsSplitTorus.relativeWeylAction_injective_of_isCompl`, which goes from the
complement to faithfulness, is not used.

## Relation to the literature

The statement's companion Markdown derives the statement from Borel–Tits,
*Groupes réductifs* (1965), Theorem 5.3 and Corollary 5.8, together with the
central/derived decomposition. The implemented route is different, and it is an
internal argument. Disjointness comes from Weyl averaging: a vector in the root
span that is fixed by a finite group negating every root must vanish. Spanning
comes from the published split-component kernel comparison. The proof does not
rely on the classical proofs that the relative roots form a root system. Its
rank-one input is the Library theorem
`rootRankOneFactorization`, whose companion Markdown cites Kaletha–Prasad
2.11.17 and Conrad–Gabber–Prasad C.2.24(i),(iii).
