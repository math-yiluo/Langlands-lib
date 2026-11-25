# Almost-simple covers of semisimple groups over a field

This module is an internal step toward the proof of
[`SimpleFactorDecompositionStatement`](SimpleFactorDecompositionStatement.md), Conrad's
decomposition theorem for semisimple groups (*Reductive group schemes*, Theorem 5.1.19,
p.150). It introduces a structure `AlmostSimpleCover G` and proves, for a semisimple `G` with
such a cover, that the factors of the cover are exactly the minimal nontrivial smooth
connected closed normal subgroups of `G`, without repetition (clause 1 of the statement), and
that every smooth connected closed normal subgroup of `G` is determined, factor by factor,
by which factors it contains. It uses the helpers of
[`SimpleFactorPoints`](SimpleFactorPoints.md). All declarations are in the namespace
`Langlands.GroupScheme.SimpleFactor`. "Range", "normal", `≤` and `⊥` refer to
`SubgroupFunctor.range`, `SubgroupFunctor.IsNormal` and the order on subgroup functors,
tested on every test scheme; `commutant` is the subgroup functor of
[`SimpleFactorPoints`](SimpleFactorPoints.md) (points commuting with all points of a given
subgroup functor).

## General facts (any base scheme)

- `commute_comp f h`: a homomorphism sends commuting points to commuting points.
- `commute_of_commute_comp f h`: a homomorphism whose underlying morphism is a monomorphism
  reflects commutation.
- `range_ne_bot_of_noncommutative j h`: a monomorphic homomorphism out of a group with two
  non-commuting points has range `≠ ⊥`.

## Predicates

For a field `k : Type u` and group schemes `H`, `K` over `Spec k`, and `n : K ⟶ H`:

- `IsNormalSmooth n` is `IsClosedSubgroup n ∧ Smooth K.X.hom ∧ ConnectedSpace K.X.left ∧
  (SubgroupFunctor.range n).IsNormal`;
- `IsMinimalNormalSmooth n` is `IsNormalSmooth n ∧ range n ≠ ⊥ ∧` every `n' : K' ⟶ H` with
  `IsNormalSmooth n'`, `range n' ≠ ⊥` and `range n' ≤ range n` has `range n' = range n`.

These are word for word the local predicates `IsNormalSubgroup` and
`IsMinimalNormalSubgroup` of `SimpleFactorDecompositionStatement`, so they agree with them
definitionally; they are named here so that lemmas can mention them.

## Semisimple facts

For `k` a field and `G`, `H`, `K` group schemes over `Spec k`:

- `range_eq_bot_of_commute hH j h`: if `H` is semisimple, `j : H ⟶ G` is monomorphic, and
  all points `x ≫ j`, `y ≫ j` commute, then `range j = ⊥`. Proof: `j` reflects commutation,
  so `H` is commutative, hence trivial by the published
  `IsSemisimple.noncommutative_of_nontrivial`.
- `range_eq_bot_of_le_commutant hG n hn h`: if `G` is semisimple, `IsNormalSmooth n`, and
  `range n ≤ commutant (range n)`, then `range n = ⊥`. Proof: `K` is semisimple by the
  published `IsSemisimple.of_normalSubgroup`; apply the previous item.
- `le_commutant_range_iff F n`: `F ≤ commutant (range n)` if and only if every point of `F`
  commutes with every point `y ≫ n` over the same test scheme.

## The structure `AlmostSimpleCover G`

An `AlmostSimpleCover G` consists of

- an index type `Index : Type u` with `Finite Index`;
- group schemes `factor i` over `Spec k` with `IsAlmostSimple (factor i)`;
- a homomorphism `mul : pi factor ⟶ G` whose underlying morphism of schemes is
  quasi-compact, flat and surjective;
- the condition that each `inclusion i := piFactorInclusionHom factor i ≫ mul` is
  `IsClosedSubgroup`.

The structure is internal to this proof. A central isogeny `pi A ⟶ G` with closed factor
maps (`exists_almostSimplePresentation` in
[`SimpleFactorPresentation`](SimpleFactorPresentation.md)) gives one; the image of a
subproduct, with its quotient map, gives another (`IsSubfamilyImage.subcover` in
[`SimpleFactorSubgroups`](SimpleFactorSubgroups.md)). Only quasi-compactness, flatness and
surjectivity of `mul` are required, which is why the same structure serves both.

## Results about a cover `D : AlmostSimpleCover G`

- `isClosedSubgroup_inclusion`, the instance `mono_inclusion`, `smooth_factor`,
  `connectedSpace_factor` (from `IsAlmostSimple`), and `comp_inclusion_hom` (unfolding the
  inclusion on points).
- `isNormal_range_inclusion i`: each factor is normal in `G`. Proof: the factor is normal in
  the product (published `isNormal_range_piFactorInclusionHom`), and conjugation in `G` lifts
  to the product along `mul` after a flat refinement (`isNormal_range_of_lift`).
- `commute_inclusion hij x y` and `range_inclusion_le_commutant hij`: distinct factors
  commute, because they commute in the product.
- `range_inclusion_ne_bot i` (factors are noncommutative) and `isNormalSmooth_inclusion i`.
- `range_le_or_le_commutant hG i n hn`: for semisimple `G` and `IsNormalSmooth n`, the
  factor `i` lies in `range n` or in `commutant (range n)`. This is the published
  `IsAlmostSimple.range_le_or_commute_of_normal`.
- `isMinimalNormalSmooth_inclusion hG i`: each factor is a minimal nontrivial smooth
  connected closed normal subgroup. If `n'` is nontrivial with `range n' ≤ range (inclusion i)`,
  the dichotomy gives either the reverse inclusion or `range n' ≤ commutant (range n')`,
  and the latter forces `range n' = ⊥`.
- `top_le_commutant F h`: if all factors lie in `commutant F`, so does all of `G`. Proof:
  the range of `mul` lies in `commutant F` (`range_le_of_forall_factor`), and this descends
  to `G` along the flat surjection `mul` (`range_le_commutant_of_comp`).
- `exists_range_eq_inclusion hG n hn`: every minimal `n` has the range of some factor. If
  not, minimality of `n` and the dichotomy put every factor in `commutant (range n)`, so
  `range n` lies in its own commutant and is `⊥`, a contradiction.
- `injective_range_inclusion hG`: distinct factors have distinct ranges (otherwise a factor
  would lie in its own commutant).
- `support n`, the set of indices `i` with `range (inclusion i) ≤ range n`, with
  `mem_support`; `range_le_commutant_of_notMem_support hG hn hi`: for `IsNormalSmooth n`, a
  factor outside the support lies in `commutant (range n)`.
- `mem_support_complement_iff hG hn hn' hc hm i`: let `n : K ⟶ G` and `n' : K' ⟶ G` satisfy
  `IsNormalSmooth`, have commuting points (`hc`), and have central-isogeny multiplication
  `commutingSubgroupMultiplicationHom n n' hc` (`hm`). Then `i ∈ support n'` if and only if
  `i ∉ support n`. If `i` were in both supports, `range (inclusion i) ≤ range n' ≤
  commutant (range n) ≤ commutant (range (inclusion i))`. If `i` were in neither, the
  factor would commute with the points of `n` and of `n'`, hence with all points of `G`,
  by `commute_of_lift` along the flat surjection `n ⊗ n' → G`. Either way the factor lies
  in its own commutant, contradicting `range_inclusion_ne_bot`.

## Provenance

The structure and the proofs are internal to this formalization. Conrad's proof of
Theorem 5.1.19 (pp.150–151) reduces to the split case over `k_s` (Proposition 5.1.17) and
uses Galois descent. The arguments here work directly over `k`, using only the published
dichotomy for almost-simple normal subgroups, semisimplicity of smooth connected normal
subgroups, and noncommutativity of nontrivial semisimple groups.
