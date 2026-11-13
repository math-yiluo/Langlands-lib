# Nesting of the chosen opposite standard parabolics

Worker 5295. This module sets up an internal construction for the proof of
Renard VII.4.2 (iii). It relates the opposite parabolics of two nested
standard parabolics. Throughout, `G` is a connected reductive group over a
field `k`, `i : T → G` is a maximal split torus, and `ν` is a generic
cocharacter. Labels `J`, `K` are subsets of the simple relative roots, of type
`StandardJacquetFamily.Index i ν`. `OppositeStandardJacquetFamily.datum`
gives the published opposite of the standard parabolic `P_J`; we write `P̄_J`
for it. Its Levi is the standard Levi `M_J`.

## Statements

All declarations live in the namespace
`Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily.Nesting`.

* `parabolic_neg_le_neg`: suppose `ζ`, `ξ` are cocharacters of `T` with
  `P(ζ) ⊆ P(ξ)`, where `P(·)` is the dynamic parabolic of the cocharacter
  composed with `i`. Then `P(-ζ) ⊆ P(-ξ)`.
* `pointImage_le_of_range_le`: an inclusion of all-test ranges of two
  subgroup morphisms into `G` gives an inclusion of their rational-point
  images.
* `realizing J`: the cocharacter of `G` that the published opposite
  construction (`DynamicLeviConjugacy.parabolicLeviRealizingCocharacter`)
  chooses for the standard datum of `J`. The two lemmas
  `standardParabolic_eq_realizing` and `standardLevi_eq_realizing` record
  that `P_J` is its dynamic parabolic and `M_J` its dynamic centralizer.
* `range_opposite_p`: the range of the opposite inclusion `P̄_J → G` is the
  dynamic parabolic of the inverse of `realizing J`.
* `exists_lattice`, `lattice J`, `lattice_comp`: `realizing J` factors
  through `T`. `lattice J` is a chosen cocharacter `ζ_J` of `T` with
  `ζ_J ≫ i = realizing J`.
* `range_opposite_p_eq`: `P̄_J = P(-ζ_J)`, as subgroup functors.
* `standardLevi_eq_neg`: `M_J` is the dynamic centralizer of `-ζ_J ≫ i`.
* `range_opposite_p_le`, `pointImage_opposite_p_le`: if `J ⊆ K`, then
  `P̄_J ⊆ P̄_K`, on every test scheme and on rational points.
* `standardLevi_le`: if `J ⊆ K`, then `M_J ⊆ M_K`.
* `leviInclusion h : M_J → M_K` (for `h : J ⊆ K`): the morphism of standard
  Levi schemes whose composite with `Standard.leviHom K` is
  `Standard.leviHom J` (`leviInclusion_comp`). It is a monomorphism
  (`mono_leviInclusion`).
* `innerCocharacter J K : 𝔾_m → M_K`: the cocharacter `-ζ_J` of `T`, composed
  with the published factorization `standardLeviTorusFactor` of `T` through
  `M_K`. Its composite with `Standard.leviHom K` is `-ζ_J ≫ i`
  (`innerCocharacter_comp`).
* `isRepresentedBy_centralizer_inner h`: `leviInclusion h` represents the
  dynamic centralizer of `innerCocharacter J K` inside `M_K`.
* `isConnectedReductive_levi J`: `M_J` is connected reductive.
* `NestedData h` (structure, `h : J ⊆ K`) has the following fields.
  * A parabolic `p : P → M_K` (`hp`). Its Levi is `m : M_J → P` (`hm`,
    a rational Levi). Its radical is `n : N → P` (`hn`, a geometric unipotent
    radical). Multiplication `M_J × N → P` is an isomorphism (`hmul`).
  * `levi_eq : m ≫ p = leviInclusion h`.
  * `range_eq`: the all-test range of `p` is the dynamic parabolic of
    `innerCocharacter J K`.
  * A morphism `e : A_K → A_J` of the split components chosen by
    `OppositeStandardJacquetFamily.component`.
  * `e_comp`: `e` composed with `a_J : A_J → M_J` and `leviInclusion h` is
    `a_K : A_K → M_K`.
  * `e_g`: `e` composed with `g_J : A_J → T` is `g_K : A_K → T`. Here
    `g_J`, `g_K` are the chosen maps into the maximal split torus.
* `nestedData h : NestedData h`: a chosen such datum.
* `NestedData.levi_comp`: `m ≫ p ≫ l_K ≫ p_K = l_J ≫ p_J`. Here `l ≫ p` is
  the ambient Levi map of an opposite datum.
* `NestedData.range_comp`: on every test scheme, the range of
  `p ≫ Standard.leviHom K` is `M_K ∩ P̄_J`.
* `NestedData.inner_eq`: on rational points,
  `image(p ≫ l_K ≫ p_K) = image(l_K ≫ p_K) ⊓ image(p_J)`. In words, the
  rational points of the inner parabolic are the points of `M_K(k)` lying in
  `P̄_J(k)`.
* `NestedData.e_comp_inner`: `e ≫ a_J ≫ m ≫ p = a_K`.

These are exactly the hypotheses `hPQ`, `hM`, `hPL` and `he` of the
published transitivity results in
`Langlands.Representation.Exponents.NestedJacquetExponentProjection`. For
example, `isNormalizedJacquetExponent_nested_of_fine` and
`isNormalizedJacquetExponent_outer_of_fine_scheme` apply with the following
data: fine datum `P̄_J`, outer datum `P̄_K`, inner datum `(p, m, n)`, split
components `A_K` and `A_J`.

## Proofs

* `parabolic_neg_le_neg` combines the published root-sign criterion
  `relativeRootSignInclusions` with `relativeRootNegation`. The criterion says
  `P(ζ) ⊆ P(ξ)` iff every relative root that is nonnegative on `ζ` is also
  nonnegative on `ξ`. Negating `ζ` and `ξ` turns this into the same condition
  for `-α`, and `-α` is again a relative root.
* `realizing`, together with its two specification lemmas, unfolds the
  published realizing cocharacter. The specification lemmas use the
  identification of the ranges of the standard datum with the standard
  parabolic and the standard Levi. `range_opposite_p` is the
  representability of the affine dynamic parabolic, because the opposite
  construction is the dynamic parabolic of `Dynamic.oppositeCocharacter`.
* `exists_lattice`: `T` lies in `M_J`, which is the centralizer of the
  realizing cocharacter. So `T` commutes with the image of `𝔾_m`, by
  `NoProperPseudoParabolicSplitTorusCentral.commute_of_mem_centralizer`.
  Maximality of `T` then gives the factorization, by
  `IsMaximalSplitTorus.exists_factor_of_commute`.
* For `range_opposite_p_eq` and `standardLevi_eq_neg`, rewrite with
  `groupHom_neg_comp_eq_oppositeCocharacter` and `lattice_comp`. The second
  also uses the fact that opposite cocharacters have the same centralizer.
* `range_opposite_p_le`: by the published `standardParabolicOrder`,
  `J ⊆ K` gives `P_J ⊆ P_K`, that is `P(ζ_J) ⊆ P(ζ_K)`. Then
  `parabolic_neg_le_neg` applies. `standardLevi_le` is the Levi half of the
  same theorem.
* `leviInclusion` factors `Standard.leviHom J` through the representing
  morphism `Standard.leviHom K`; this uses `standardLevi_le`. Monicity
  follows from monicity of `Standard.leviHom J`.
* `isRepresentedBy_centralizer_inner`: `Standard.leviHom K` is a closed
  subgroup. So the dynamic centralizer in `M_K` is the comap of the dynamic
  centralizer in `G` of `-ζ_J ≫ i`, which is `M_J` by `standardLevi_eq_neg`.
  The comap of `M_J` along `M_K` is the range of `leviInclusion`, because
  `Standard.leviHom K` is a monomorphism.
* `nestedData` applies the affine dynamic construction inside `M_K` to the
  inner cocharacter. This is the same template as the published
  `oppositeLeviParabolic`. The parabolic and unipotent schemes of the
  cocharacter give `p` and the radical. Representability of the centralizer
  by `leviInclusion` gives `m` with `m ≫ p = leviInclusion h`. The published
  results `dynamicGeometricUnipotentRadical`,
  `Dynamic.isIso_subgroupMultiplication`,
  `Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical` and
  `isParabolicSubgroup_of_range_eq_dynamicParabolic` give the remaining
  properties; `M_K` and `M_J` are connected reductive.
  For `e`, the composite `g_K ≫ standardLeviTorusFactor J : A_K → M_J` is
  central, because its composite with the monomorphism `leviInclusion h` is
  the central `a_K`. `A_K` is a split torus, so it factors through the
  split component `A_J` (`IsSplitComponent.exists_factor`). That gives
  `e_comp`. `e_g` follows by cancelling the monomorphism `i`, using the
  factorization of `a_J` through `g_J` and `standardLeviTorusFactor_comp`.
* `levi_comp` rewrites both ambient Levi maps to `Standard.leviHom`
  (`datum_l_comp_p`), then uses `levi_eq` and `leviInclusion_comp`.
  `range_comp` combines three facts: the range of a composite with a closed
  subgroup is a map of ranges; `range_eq`; and
  `Dynamic.range_inf_parabolic`, which says the dynamic parabolic of a
  subgroup's cocharacter is the intersection with the ambient dynamic
  parabolic. Then `innerCocharacter_comp` and `range_opposite_p_eq` apply.
  `inner_eq` is `range_comp` evaluated at the base scheme.
  `e_comp_inner` is `levi_eq` followed by `e_comp`.

## Provenance

This is internal infrastructure (derived provenance) for the proof of
Renard VII.4.2 (iii) (printed p.244 / PDF p.250). That proof uses the
following setup. For standard parabolics `P_J ⊆ P_K = Q`, the opposite
`P̄_J` lies in `Q̄`, and `P̄_J ∩ M_K` is a parabolic of `M_K` with Levi
`M_J`. Exponents are then restricted along the inclusion `A_K → A_J` of
split components, using Lemma VII.1.1 (printed pp.220–221 / PDF pp.226–227)
and the transitivity of Jacquet functors. The source treats this setup as
standard; here it is made explicit for the chosen opposite data of
`OppositeStandardJacquetFamily`. The split-component map `e` replaces the
literal inclusion `A_K ⊆ A_J` of the source, since the chosen split
components are abstract schemes with central embeddings. Source:
`renard-2026-representations-groupes-reductifs-padiques`.
