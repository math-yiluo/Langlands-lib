# Splitting a smooth representation along disjoint support categories

Worker 4195. This module proves a conditional form of Renard, Théorème VI.7.2,
for the generic standard families of `Langlands.Aubert.General`. The theorem is
grouped by an equivalence relation on standard index sets. It also proves the
splitting lemma and the direct-sum lemmas that the argument uses. Nothing here
proves the embedding, the support of induced cuspidal objects or the
association of cuspidal data. These are explicit hypotheses of
`supportCategoryDecomposition_of_inducedEmbedding`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
version dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The
relevant parts are Théorème VI.7.2 and its proof (printed pp. 182–185 / PDF
pp. 188–191) and Lemme A.IX (printed p. 268 / PDF p. 274).

## Smooth-representation lemmas (`Langlands.SmoothRep`)

* `isSubquotient_image_comp`: the image of `h ≫ g` is an actual subquotient
  of the image of `h`.
* `eq_bot_of_forall_not_isSubquotient`: an invariant submodule with no
  irreducible actual subquotient is zero. It uses the published
  `exists_isIrreducible_isSubquotient_of_nontrivial`.
* `mem_range_of_splitting`: the form of Lemme A.IX used in the proof of VI.7.2.
  Let `p, p'` be endomorphisms of `D` with `p + p' = 1`. Suppose that every
  irreducible subquotient of the image of `p` satisfies `𝒜`, that every
  irreducible subquotient of the image of `p'` satisfies `ℬ`, and that no
  irreducible object satisfies both. Then for every intertwiner `f : E ⟶ D`,
  `p` maps the image of `f` into itself. Proof: compose with the quotient map
  `q : D → D / f(E)`. Then `f ≫ p ≫ q = -(f ≫ p' ≫ q)`, so both have the same
  image. If `p (f v)` were outside `f(E)`, this image would be nonzero and would
  have an irreducible subquotient. Through `isSubquotient_image_comp`, that
  subquotient would be a subquotient of both the image of `p` and the image of
  `p'`, a contradiction.
* `directSumFilter A Q`: the equivariant projection of the actual finite direct
  sum `directSum A` onto the summands with index in `Q`. Its linear map is
  Mathlib's `DFinsupp.filterLinearMap`. With it come `directSumFilter_add_not`
  (complementary filters add to the identity), `sum_directSumFilter_fiber`
  (the filters along the fibres of a map into a finite set `s` add to the
  identity), and `range_directSumFilter_le` (the image of a filter lies in the
  invariant sum of the selected summands).
* `exists_isSubquotient_of_isSubquotient_image_directSumFilter`: an irreducible
  subquotient of the image of a filter is a subquotient of one selected
  summand. It uses the published `irreducibleSubquotient_iSup`.

## Support-category results (`Langlands.Aubert.General`)

`exists_isAssociate_of_isInSupportCategory` derives one consequence of
Théorème VI.5.4, read on support categories. If an irreducible `π` lies in
`Alg({I})` and in `Alg({J})`, then `IsAssociate I J n` for some `n`. Its inputs
are `CuspidalSupportAssociationTarget`, transport of `IsLeviCuspidal` along
association, and inversion and composition of association representatives.
The proof applies the association target to the two conjugated cuspidal data
that membership supplies. Their irreducibility comes from the published
`Langlands.isIrreducible_comp_continuousMulEquiv_iff`. The resulting
representatives are then composed.

`supportCategoryDecomposition_of_inducedEmbedding` proves
`SupportCategoryDecompositionTarget` for a finite index type from the
following explicit inputs:

1. `r`, an equivalence relation on `Finset ι`;
2. `hInv`: `Alg({I}) ⊆ Alg({J})` whenever `r I J`;
3. `hDisj`: an irreducible object in `Alg({I})` and `Alg({J})` forces `r I J`;
4. `hInd`: `InducedCuspidalSupportCategoryTarget`, that is,
   `i_K(τ) ∈ Alg({K})` for every inside-Levi cuspidal `τ`;
5. `hEmb`: `FiniteCuspidalInducedEmbeddingTarget`, an injective intertwiner
   `f : E → ⊕_K i_K(τ_K)` with all `τ_K` inside-Levi cuspidal.

The proof follows Renard's grouping by components. The class representative
`rep I` is `Quotient.out` of the class of `I`. For a representative `I`, `S I`
is the published `supportSubrepresentationSum` for `I`, the sum of all
subrepresentations lying in `Alg({I})`. For every other `I`, `S I = ⊥`. Each
`S I` lies in `Alg({I})` by the published
`isInSupportCategory_supportSubrepresentationSum`, or trivially when it is
zero.

* Independence: an irreducible subquotient of `S I ⊓ ⨆_{J ≠ I} S J` is a
  subquotient of `S I` and of some `S J` with `J ≠ I`. If both are
  representatives, `hDisj` makes them equivalent and hence equal, a
  contradiction. Otherwise one of the two is `⊥`. So the intersection is zero by
  `eq_bot_of_forall_not_isSubquotient`.
* Spanning: let `D = ⊕_K i_K(τ_K)` and let `p_I` be the filter onto the summands
  `K` with `rep K = I`. By `hInd`, `hInv` and the direct-sum lemma, the
  irreducible subquotients of the image of `p_I` lie in `Alg({I})`, and those
  of the image of the complementary filter lie in `Alg({rep K})` for some
  representative `rep K ≠ I`. By `hDisj` no irreducible object is in both.
  `mem_range_of_splitting` then gives `e_I ∈ E` with `f(e_I) = p_I(f v)`.
  `e_I` lies in the preimage of the image of `p_I`, which lies in `Alg({I})`
  because `f` is injective, so `e_I ∈ S I`. Summing over representatives and
  using `sum_directSumFilter_fiber` and injectivity of `f` gives
  `v = ∑_I e_I`.

Together these give `DirectSum.IsInternal` through Mathlib's
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`.

No finite-length, admissibility or finite-generation hypothesis appears. The
universe pattern matches the published targets. With `ι : Type uG`, the
decomposition target is used at `.{uG, uG, uV}` and the embedding target at
`.{uG, uG, max uG uV}`, so the inducing carriers lie in `Type (max uG uV)`.
