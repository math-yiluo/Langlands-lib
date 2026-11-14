# Fundamental-group comparisons and induced maps with torus target

Author: Worker 5168.

This internal module proves, without hypotheses, the special cases of the
canonical-comparison and induced-map laws of KP Construction 11.3.1 and
Lemma 11.3.6 that are needed when the target group is a torus. Here KP is
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), printed
pp. 427–430 / PDF pp. 458–461. For general targets, those laws are the
unproved `AlgebraicFundamentalGroupComparisonStatement` and
`AlgebraicFundamentalGroupMapStatement`. This module proves neither general
statement. It covers every choice of presentation for a torus target, and
every morphism from a group into a torus.

Everything works over an arbitrary field `k : Type u` and an arbitrary field
extension `E/k`. `E` need not be separably closed. `T` is an actual commutative
group scheme over `Spec k` with `hT : IsTorus T.toGrp`. All maps are actual
group-scheme morphisms and their base changes along `algebraBaseMap k E`.

## Declarations

- `innerIso_hom_eq_id_of_commGroupScheme`: the inner automorphism of a
  commutative group scheme over any base, by any base point, is the identity.
  On points it is conjugation in a commutative group.
- `inclusionIso hT b`: for a `Choice` `b` of the torus `T`, the inclusion of
  its maximal torus is an isomorphism (`IsMaximalTorus.isIso_of_torus`).
  This packages that inclusion as an isomorphism.
- `torusTargetHom hT a c f`: let `a` be a choice for any group scheme `H`, `c`
  a choice for `T`, and `f : H ⟶ T.toGrp` a homomorphism. This is the actual
  homomorphism of commutative group schemes `a.torus → H → T ≅ c.torus`, the
  last map being the inverse of `c`'s inclusion.
  `torusTargetHom_comp_inclusion` records its defining square. For two choices
  `b', b` of `T`, `torusChoiceIso hT b' b` is the isomorphism
  `b'.torus ≅ b.torus` with hom `torusTargetHom hT b' b (𝟙 _)`.
  `torusTargetHom_id_self` shows that it is the identity when `b' = b`.
- `groupHom_baseChange_torusTargetHom_comp` gives the base-changed square, and
  `eq_of_groupHom_comp_inclusion` cancels the base-changed inclusion of `c`,
  which is an isomorphism.

### Canonical comparisons of a torus

`exists_isCanonicalComparison_of_isTorus` shows that any two choices `b', b` of
`T` have a canonical comparison in the sense of `Choice.IsCanonicalComparison`.
The conjugator is the identity point, and `innerIso_one_hom` gives the required
conjugation square. The torus isomorphism is the base change of
`torusChoiceIso`. Both coroot images are zero
(`torusChoice_corootImage_eq_bot`), so the quotient map is a lift of the
induced map on cocharacters.

`comparison_projection_of_isTorus` evaluates the epsilon-selected
`b'.comparison E b` on representatives. It sends the class of `ν` to the class
of `ν ≫ (torusChoiceIso hT b' b).hom_E`. The selected comparison comes with
some conjugator `g` and some torus isomorphism `e`. Since `T_E` is commutative,
`Int(g)` is the identity. The conjugation square then says that `e`, followed
by the base-changed inclusion of `b`, equals the base-changed inclusion of
`b'`. Cancelling that isomorphism identifies `e` with the base change of
`torusChoiceIso`. `comparison_self_of_isTorus` concludes that
`b.comparison E b = LinearMap.id`.

### Induced maps into a torus

Now `a : Choice k H`, `c : Choice k T.toGrp` and `f : H ⟶ T.toGrp`.

- `scToTorus_comp_torusTargetHom`: `torusTargetHom hT a c f` kills the actual
  preimage torus `T_sc` of `a`. The map `T_sc → a.torus → H` factors through
  the derived inclusion of `a`. The published `IsDerivedSubgroup.comp_eq_one`
  makes the derived subgroup trivial in the commutative separated target `T`.
- `torusTargetInducedMap E hT a c f`: the linear map
  `X_*(T_a)/X_*(T_sc) → c.atChoice E` sending the class of `ν` to the class of
  `ν ≫ (torusTargetHom hT a c f)_E`. The preceding lemma makes it well defined.
- `isTorusFactorization_torusTargetHom`: the base change of `torusTargetHom`
  is a geometric torus factorization of `f` through `c`.
- `comparison_projection_of_isTorusFactorization`: let `b` be any choice of `T`
  and `e` any geometric factorization of `f` through `b`. Then
  `b.comparison E c` sends the class of `ν ≫ e` to the class of
  `ν ≫ (torusTargetHom hT a c f)_E`. The proof uses the comparison formula
  above and cancels the base-changed inclusion of `c`.
- `isInducedMap_torusTargetInducedMap`: the explicit map satisfies the full
  `Choice.IsInducedMap` law, for every choice of the target torus and every
  factorization. Hence `isInducedMap_mapTo_of_isTorus` shows that the
  epsilon-selected `a.mapTo E c f` satisfies its law. Its value on
  representatives is `mapTo_projection_of_isTorus`, and
  `mapTo_eq_torusTargetInducedMap` identifies it with the explicit map.
- `mapTo_galois_of_isTorus`: `a.mapTo E c f` intertwines the descended Galois
  representations of `a` and `c`. On representatives this is naturality of
  cocharacter transport for the actual morphism `torusTargetHom`, which is the
  published `geometricCocharacterMap_galois`.

## Use and provenance

`fundamentalGroupMap k E H T.toGrp hH hT' f` is by definition
`(chosenChoice k H hH).mapTo E (chosenChoice k T.toGrp hT') f`. The results
above therefore give its representative law and Galois equivariance whenever
the target is a torus, such as the actual cocenter of a reductive group. The
torus self-comparison is also identified. These are the three facts that
`CocenterTargetTorsionReduction` takes from the two general statements.

The provenance is internal. The results are derived from the Library's
definitions of `Choice`, `IsCanonicalComparison`, `IsInducedMap`, `comparison`
and `mapTo`, together with the published lemmas named above. The mathematical
content is the elementary observation that for a torus target, conjugation is
trivial and all maximal-torus inclusions are isomorphisms. Under KP's
identification `π₁(T) = X_*(T)` (Fact 11.3.5), the map of Lemma 11.3.6 induced
by `f` is then `ν ↦ ν ≫ f`. The module makes no further literature assertion.
