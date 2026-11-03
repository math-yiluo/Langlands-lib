# Scheme-theoretic centre field base change: proof

Author: Worker 1401.

This module proves `Langlands.GroupScheme.SchemeTheoreticCenterBaseChangeStatement`,
stated in `Langlands.GroupScheme.Reductive.CenterStructureStatement`. The theorem
`Langlands.GroupScheme.schemeTheoreticCenterBaseChangeStatement` has exactly that
statement as its type, at arbitrary universe `u`.

## Main theorem

Let `k K : Type u` be fields with `Algebra k K`. Let `G Z` be group schemes over
`Spec k` and `z : Z ⟶ G` with `IsSchemeTheoreticCenter z`. Write `b` for
`algebraBaseMap k K`. The predicate `IsSchemeTheoreticCenter` has two parts, and
the proof establishes both for the pulled-back homomorphism
`(GroupScheme.baseChange b).map z`:

- Closedness comes from the existing `IsClosedSubgroup.baseChange` in
  `Langlands.GroupScheme.SubgroupBaseChange`: closed immersions are stable under
  pullback.
- For the range equality, the proof rewrites with three equalities:
  `SubgroupFunctor.range_baseChangeHom` (range commutes with base change), the
  hypothesis `range z = center G`, and `center_baseChange` from this module.

The premise `IsConnectedReductive G` is not used. The proof does not need
smoothness or reducedness of `Z`, and it places no condition on the extension
`K / k`. Nonreduced centres such as `μ_p` therefore need no special treatment.
The conclusion keeps the actual pulled-back homomorphism `Z_K ⟶ G_K` and the full
all-test functor `center G_K`.

## The centre functor commutes with base change

`center_baseChange b G` proves
`center ((GroupScheme.baseChange b).obj G) = (center G).baseChange b` for any
morphism of schemes `b : S' ⟶ S` and any group scheme `G` over `S`. The functor
`center` quantifies over every later test scheme. A test scheme over a scheme `T`
that lies over `S'` is again a scheme over `S'`, so the two all-test conditions
match. The proof uses the multiplicative pullback-adjunction equivalence
`baseChangePointsEquiv b G T : (T ⟶ G_{S'}) ≃* ((Over.map b).obj T ⟶ G)` and
its naturality `baseChangePointsEquiv_naturality`. It goes point by point after
`SubgroupFunctor.ext`:

- Centre of `G_{S'}` ⊆ base change of the centre. Take a point `x` over `T` that
  is central in `G_{S'}`, a test scheme `U` over `S`, a morphism
  `c : U ⟶ (Over.map b).obj T` and a point `h : U ⟶ G`. Give `U` the structure
  `U'` over `S'` through `c.left ≫ T.hom`, and let `a : U' ⟶ T` be the morphism
  with underlying map `c.left`. Let `e : U ≅ (Over.map b).obj U'` be the
  identity on underlying schemes. Its compatibility is `Over.w c`, and it satisfies
  `e.hom ≫ (Over.map b).map a = c`. Centrality of `x` at `a` and
  `(baseChangePointsEquiv b G U').symm (e.inv ≫ h)` gives a commuting pair.
  Mapping it through the equivalence, with naturality, gives
  `Commute ((Over.map b).map a ≫ x') (e.inv ≫ h)`, where `x'` is the image of
  `x`. Precomposing with `e.hom` then gives `Commute (c ≫ x') h`. The helper
  `commute_comp` says that precomposition preserves commuting pairs, by
  `MonObj.comp_mul`.
- Base change of the centre ⊆ centre of `G_{S'}`. Take a test morphism
  `a : T' ⟶ T` over `S'` and a point `h` over `T'`. Apply centrality in `G` to
  `(Over.map b).map a` and the image of `h`. Naturality rewrites the first factor
  as the image of `a ≫ x`. Mapping back through the inverse equivalence gives
  `Commute (a ≫ x) h`.

## Relation to the sources

The statement's Markdown cites Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
2nd ed., Definitions A.1.9–A.1.10 (printed pp.468–469), and Milne, *Algebraic
Groups* (2017), 17.62. Both say that forming the centre commutes with extension
of the ground field. Those sources describe the centre through closed subschemes
and coordinate algebras. Here the centre is the published all-test functor
`center`, and the representing subgroup is given as a hypothesis. In this
setting the comparison is the formal argument above. All representability
content belongs to the separate existence target
`SchemeTheoreticCenterExistenceStatement`, which this module does not prove.
