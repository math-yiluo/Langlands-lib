# Existence and uniqueness of the split component

Author: Worker 1178.

This file proves `Langlands.GroupScheme.SplitComponentStatement` as the
theorem `Langlands.GroupScheme.splitComponentStatement`, for every universe
`u`, every field `k` and every `G : GroupScheme (Spec (CommRingCat.of k))`
with the published `IsConnectedReductive G`. No splitness, perfectness,
characteristic or local-field hypothesis is added, and no property of the
centre (such as smoothness) is used.

## Source and route

Renard, *Représentations des groupes réductifs p-adiques* (2026), V.2.1,
printed p.104 (source `renard-2026-representations-groupes-reductifs-padiques`),
defines the split component as a maximal split torus in the centre and
deduces uniqueness from conjugacy by `R(G)`. The scope over an arbitrary field
is the derived scope recorded in `Rational/CharactersStatement.md`. The Lean
proof does not use conjugacy. It proves directly, over every field, that an
affine group scheme of finite type has a *largest* central split torus, and
derives both clauses from that. Of `IsConnectedReductive G` it uses only that
`G` is affine over `k` and smooth, hence locally of finite type.

## The proof

- `finiteType_coordinateAlgebra`: for `G` affine and locally of finite type,
  the coordinate algebra of the Library's `AffineCoordinates` model of `G` is
  of finite type (`HasRingHomProperty.Spec_iff`, transported along
  `AffineCoordinates.groupSchemeIso`).
- `exists_largestCentralSplitTorus`: apply `exists_universal`
  (`SplitComponent/LargestTorus`) to the corepresentation of `G`. With
  `torusIso` and `groupSchemeIso` this gives `j : 𝔾_m^J ⟶ G` which is a split
  torus, a closed subgroup (surjective classifying map), and central. Given a
  central `i : A ⟶ G` with `A ≅ 𝔾_m^I`, transport `i` to a homomorphism of
  corepresented group schemes, write it as `groupSchemeMap` of a central
  natural homomorphism (`natOfHom`), factor that through `j`, and transport
  back with `groupSchemeMap_comp`.
- Helper lemmas: the Library's `IsClosedSubgroup.comp_iso`
  (`Rational/SplitRankTransport`) and `IsCentral.comp_iso`
  (`CorepresentedComultiplication`) preserve closedness and centrality under
  postcomposition with an isomorphism. The private `IsClosedSubgroup.cancel`
  proves that a closed subgroup is a monomorphism, since closed immersions
  are monomorphisms of schemes.

`splitComponentStatement`:

- *Existence.* `j` is a split component: if `f ≫ i' = j` with `i'` a central
  split torus, the largest property gives `g` with `g ≫ j = i'`; cancelling
  the closed subgroups `j` and `i'` gives `f ≫ g = 𝟙` and `g ≫ f = 𝟙`.
- *Uniqueness.* For split components `i : A ⟶ G` and `i' : A' ⟶ G`, write
  `i = g ≫ j` and `i' = g' ≫ j`. Maximality of `i` and `i'`, applied to the
  central split torus `j`, makes `g` and `g'` isomorphisms, and
  `e = g ≫ g'⁻¹` satisfies `e.hom ≫ i' = i`.

## Supporting modules

`SplitComponent/LatticeFunctor`, `SplitComponent/LatticeImage`,
`SplitComponent/ImageTorus`, `SplitComponent/RankBound`,
`SplitComponent/LargestTorus` and `SplitComponent/SchemeBridge`; their paired
Markdown files describe the constructions.
