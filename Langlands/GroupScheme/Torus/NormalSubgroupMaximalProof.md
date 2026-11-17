# Maximal tori of a normal subgroup variety: proof

Author: Worker 752.

`Langlands.GroupScheme.normalSubgroupMaximalTorus` proves the published
`Langlands.GroupScheme.NormalSubgroupMaximalTorusStatement.{u}`
([`Torus.NormalSubgroupMaximalStatement`](NormalSubgroupMaximalStatement.md)) for every
universe `u`, with no additional hypotheses:

```lean
theorem normalSubgroupMaximalTorus : NormalSubgroupMaximalTorusStatement.{u}
```

Let `k` be a field and `G` a smooth affine group scheme over `Spec k` whose underlying space is
connected. Let `n : N ⟶ G` be a closed subgroup with `N` smooth and
`(SubgroupFunctor.range n).IsNormal`. The theorem gives:

1. every maximal torus `j : T ⟶ G` contains a maximal torus `s : S ⟶ N` of `N`, in the sense
   `SubgroupFunctor.range (s ≫ n) ≤ SubgroupFunctor.range j`;
2. every maximal torus `s : S ⟶ N` of `N` lies, in the same sense, in a maximal torus of `G`.

This is Milne, *Algebraic Groups* (2017), Corollary 17.85, in the containment form used by the
statement module (its Markdown explains why this form is equivalent to Milne's wording). The
proof combines published Library results. The module adds the small auxiliary lemmas listed
below, all in the namespace `Langlands.GroupScheme.NormalSubgroupMaximalTorus`.
`lean_check` of the module reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Auxiliary lemmas

- `range_comp_le (f : A ⟶ B) (g : B ⟶ C)`: `range (f ≫ g) ≤ range g`, over any base scheme. A
  point `y ≫ (f ≫ g)` is the point `(y ≫ f) ≫ g`. (The same fact exists as
  `SubgroupFunctor.range_comp_le` in an unrelated module; it is restated here to avoid that
  import.)
- `isRelativeMultiplicativeType_of_isClosedSubgroup (hT : IsTorus T) (i : H ⟶ T)
  (hi : IsClosedSubgroup i) : RelativeMultiplicativeType.IsMultiplicativeType H`: a closed
  subgroup of a torus over a field is of multiplicative type in the relative (fppf-local)
  sense. `torusFiniteGaloisSplitting` gives a finite Galois extension `K/k` splitting `T`. The
  map `b : Spec K ⟶ Spec k` is étale (finite separable extension), hence flat and locally of
  finite presentation, and it is surjective (`fieldExtension_fpqc`). So `b` alone is an fppf
  cover, built with `Scheme.Cover.mkOfCovers`. Over `K`, the base change of `i` is a closed
  subgroup of a split torus, so `exists_diagonalizableIso_of_isClosedSubgroup_splitTorus`
  identifies the base change of `H` with `Diagonalizable.groupScheme K Λ` for a finitely
  generated abelian group `Λ`. `Diagonalizable.baseChangeIso` identifies this with
  `diagonalizable (Spec K) Λ`, which is the required diagonalizability.
- `exists_isMaximalTorus_range_le_of_subgroup`: part 2, for any closed subgroup `n` of a
  smooth affine `G` (neither normality nor connectedness is used). The closed torus `s ≫ n` of
  `G` extends to a maximal torus `j` of `G` with `f ≫ j = s ≫ n`
  (`exists_maximalTorus_extension_of_finiteType`); then `range (s ≫ n) = range (f ≫ j) ≤
  range j` by `range_comp_le`.
- `subgroupIntersectionBaseChangeIso_inv_snd`: the inverse of the comparison isomorphism
  `subgroupIntersectionBaseChangeIso b j j'` between the base change of the intersection and
  the intersection of the base changes, followed by the base change of the second projection,
  is the second projection. It is `PreservesPullback.iso_inv_snd`.
- `isMaximalTorus_of_comp_eq`: over a field, if `s : S ⟶ N` is a closed subgroup with `S` a
  torus, `s₁ : S₁ ⟶ N` is a maximal torus and `a ≫ s = s₁`, then `s` is a maximal torus.
  Maximality of `s₁` makes `a` an isomorphism, and `IsMaximalTorus.iso_comp` transports
  maximality along `a⁻¹` to `a⁻¹ ≫ s₁ = s`.
- `exists_conjugate_maximalTorus_factor`: over an algebraically closed field, let `G` be
  smooth, affine and connected, `n : N ⟶ G` closed with normal range, `j : T ⟶ G` and
  `j₀ : T₀ ⟶ G` maximal tori, `s₀ : S₀ ⟶ N` a maximal torus of `N` and `f₀ ≫ j₀ = s₀ ≫ n`.
  Then there are a maximal torus `s₁ : S₀ ⟶ N` of `N` and `t : S₀ ⟶ T` with
  `t ≫ j = s₁ ≫ n`. Proof: `maximalTorusConjugacy` (Milne 17.10) gives a point `g` of `G` and
  `φ : T₀ ≅ T` with `j₀ ≫ inn(g) = φ ≫ j`. Since `n` represents its normal range
  (`IsClosedSubgroup.isRepresentedBy_range`), conjugation by `g` restricts to an automorphism
  `c = conjugateIso` of `N` with `c ≫ n = n ≫ inn(g)`. Take `s₁ = s₀ ≫ c`, maximal by
  `IsMaximalTorus.comp_iso`, and `t = f₀ ≫ φ`: then
  `t ≫ j = f₀ ≫ j₀ ≫ inn(g) = s₀ ≫ n ≫ inn(g) = s₁ ≫ n`.

## Part 1: `exists_isMaximalTorus_range_le_of_normal`

Let `j : T ⟶ G` be a maximal torus.

1. **The intersection `T ∩ N`.** Let `H = subgroupIntersection j n` (the pullback of `j` and
   `n`), with projections `p : H ⟶ T` and `q : H ⟶ N`, so `p ≫ j = q ≫ n`. Both are closed
   immersions, as base changes of the closed immersions `n` and `j`
   (`isClosedSubgroup_subgroupIntersectionFst`, and `MorphismProperty.of_isPullback` with
   `subgroupIntersection_isPullback_scheme` for `q`).
2. **Its largest subtorus.** By `isRelativeMultiplicativeType_of_isClosedSubgroup` applied to
   `p`, `H` is of relative multiplicative type, so
   `IsMultiplicativeType.exists_universalSubtorus` gives `u : U ⟶ H` with
   `IsUniversalSubtorus u`: `u` is a closed subgroup, `U` is a relative torus, and after any
   base change every homomorphism from a relative torus into `H` factors through `u`. This
   `U` plays the role of Milne's `(T ∩ N)_t`. Let `S` be `U` with its commutative structure
   (`RelativeTorus.IsTorus.commGroupScheme`) and `s = u ≫ q : S ⟶ N`. Then `S` is a torus over
   the field (`RelativeTorus.IsTorus.isTorus`), `s` is a closed subgroup, and
   `s ≫ n = (u ≫ p) ≫ j`, so `range (s ≫ n) ≤ range j` by `range_comp_le`.
3. **Reduction to an algebraic closure.** Let `K = AlgebraicClosure k`,
   `b = toAlgebraicClosure k : Spec K ⟶ Spec k`, and write `(-)_K` for base change along `b`.
   By `maximalTorusBaseChange` (Milne 17.82) for the smooth affine group `N`, it suffices to
   show that `s_K` is a maximal torus of `N_K`. The group `G_K` is smooth and affine (base
   change of the structure morphism) and connected
   (`connectedSpace_baseChange_of_smooth_affine`), and `range n_K` is normal
   (`SubgroupFunctor.range_baseChangeHom` and `SubgroupFunctor.IsNormal.baseChange`).
4. **A maximal torus of `N` inside `T` over `K`.** `maximalTorusExistence` gives a maximal
   torus `s₀ : S₀ ⟶ N`; `exists_maximalTorus_extension_of_finiteType` puts it inside a maximal
   torus `j₀ : T₀ ⟶ G` of `G` with `f₀ ≫ j₀ = s₀ ≫ n`. By `maximalTorusBaseChange`, `j_K`,
   `(j₀)_K` and `(s₀)_K` are maximal tori over `K`. `exists_conjugate_maximalTorus_factor`
   over `K` gives a maximal torus `s₁ : (S₀)_K ⟶ N_K` and `t : (S₀)_K ⟶ T_K` with
   `t ≫ j_K = s₁ ≫ n_K`.
5. **It lies in the universal subtorus.** The pair `(t, s₁)` gives a map
   `(S₀)_K ⟶ subgroupIntersection j_K n_K` with second projection `s₁`. Composing with the
   inverse of `subgroupIntersectionBaseChangeIso b j n` gives `w : (S₀)_K ⟶ H_K` with
   `w ≫ q_K = s₁` (`subgroupIntersectionBaseChangeIso_inv_snd`). `(S₀)_K` is a torus over `K`
   (`IsTorus.baseChange`), hence a relative torus (`IsTorus.isRelativeTorus`), so the
   universal property of `u` along `b` gives `a : (S₀)_K ⟶ U_K` with `a ≫ u_K = w`. Hence
   `a ≫ s_K = a ≫ u_K ≫ q_K = s₁`.
6. **Conclusion.** `S_K` is a torus and `s_K` a closed subgroup (`IsClosedSubgroup.baseChange`),
   and the maximal torus `s₁` factors through it. By `isMaximalTorus_of_comp_eq`, `s_K` is a
   maximal torus of `N_K`, so `s` is a maximal torus of `N`.

So the proof shows slightly more than part 1 asks: the universal subtorus of the
scheme-theoretic intersection `T ∩ N` is itself a maximal torus of `N`.

## Final theorem

`normalSubgroupMaximalTorus` introduces the data and returns the pair
`⟨exists_isMaximalTorus_range_le_of_normal …, exists_isMaximalTorus_range_le_of_subgroup …⟩`.

## Comparison with Milne's proof

Milne (p.380) takes a maximal torus `T'` of `N` inside a maximal torus `T''` of `G`, conjugates
`T''_{k^a}` onto `T_{k^a}` by `g ∈ G(k^a)` (17.10), and computes
`((T ∩ N)_t)_{k^a} = (T_{k^a} ∩ N_{k^a})_t = g T'_{k^a} g⁻¹`, maximal in `N_{k^a}`; then 17.82
descends maximality. The Lean proof follows the same route with these differences:

- `(T ∩ N)_t` is the universal subtorus of the relative theory
  (`Torus.RelativeLargestSubtorusProof`). The proof never computes
  `((T ∩ N)_t)_{k^a}`: it uses only that the conjugate of `T'_{k^a}` factors through
  `((T ∩ N)_t)_{k^a}` by the universal property, and then maximality of that conjugate.
- Conjugation of the subgroup `N` by `g` is the automorphism `conjugateIso` of `N`, which
  exists because the range of `n` is normal on all test schemes.
- Part 2 uses `exists_maximalTorus_extension_of_finiteType` directly, without describing the
  torus as `(T ∩ N)_t`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`: Corollary 17.85
and its proof, p.379–380; Theorem 17.82 (maximality under field extension) and Theorem 17.10
(conjugacy of maximal tori over an algebraically closed field), used through the Library
results `maximalTorusBaseChange` and `maximalTorusConjugacy`. The source citations for the
statement are in [`NormalSubgroupMaximalStatement.md`](NormalSubgroupMaximalStatement.md).
