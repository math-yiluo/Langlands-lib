# Induced Galois maps on algebraic fundamental groups

Author: Worker 235 (Task 6357).

## Statement proved

`Langlands.GroupScheme.AlgebraicFundamentalGroup.algebraicFundamentalGroupMap`
proves the published proposition
`Langlands.GroupScheme.AlgebraicFundamentalGroup.AlgebraicFundamentalGroupMapStatement`
from `Langlands.GroupScheme.AlgebraicFundamentalGroupFunctorStatement`.

Let `k` be any field, `E` a separable closure of `k`, and `f : H ⟶ G` a
morphism of connected reductive group schemes over `k`. For arbitrary
torus/cover presentations `a : Choice k H` and `c : Choice k G`, the theorem
proves:

- unique existence of an integral linear map
  `a.atChoice E →ₗ[ℤ] c.atChoice E` satisfying `a.IsInducedMap E c f`;
- that the selected map `a.mapTo E c f` satisfies this predicate;
- equivariance of the selected map for the ordinary Galois actions of
  `E ≃ₐ[k] E`;
- compatibility with every simultaneous change `a'`, `c'` of source and
  target presentations:
  `comparison(c,c') ∘ mapTo(a,c,f) = mapTo(a',c',f) ∘ comparison(a,a')`.

The quotients are the actual integral cocharacter quotients by the images
of the preimage tori in the simply connected derived covers. The
`IsInducedMap` predicate includes existence of an actual containing maximal
torus factorization. For every such geometric factorization `e` through a
target presentation `b`, it requires
`m([ν]) = comparison(b,c)([ν ≫ e])`.
Both maximal tori and derived-cover presentations may vary.

## Proof

The Lean proof applies the published reduction
`algebraicFundamentalGroupMap_of_comparison` from
`Langlands.GroupScheme.AlgebraicFundamentalGroupMapNaturality` to the
published theorem `algebraicFundamentalGroupComparison` from
`Langlands.GroupScheme.AlgebraicFundamentalGroupComparisonProof`:

```lean
algebraicFundamentalGroupMap_of_comparison algebraicFundamentalGroupComparison
```

The reduction constructs a quotient map using the lift of `f` to the
simply connected derived covers and the resulting map of preimage tori.
This map preserves the coroot images. Relative conjugacy of maximal split
tori containing the same image, together with canonical comparisons,
makes the map independent of every containing-torus factorization.
Surjectivity of the quotient projection proves uniqueness, and existence
justifies the epsilon selection law for `mapTo`.

A factorization over the original field and naturality of cocharacter
Galois transport prove equivariance. For presentation compatibility, a
source conjugator extends to a compatible target conjugator; the
comparison formulas on cocharacter representatives then give the stated
equality. The comparison theorem supplies all comparison hypotheses of
the reduction, so the resulting theorem has no additional premises.

## Source and provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Construction
11.3.1 and Lemma 11.3.6, printed pp. 427–428 / PDF pp. 458–459. The source
constructs the quotient comparisons and the induced map by choosing a
containing maximal torus and descending its cocharacter map. This final
module assembles the existing Library proofs of that construction and its
comparison laws; it introduces no new geometric assumption.
