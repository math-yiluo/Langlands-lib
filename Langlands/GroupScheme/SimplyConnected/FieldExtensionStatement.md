# Field-extension compatibility of semisimplicity, simple connectedness and covers

This module states three propositions and their package. It proves nothing.
Each component quantifies over a universe `u`, fields `k K : Type u` and an
arbitrary `Algebra k K`. The extension `K/k` need not be algebraic, separable,
finite, perfect or algebraically closed, and either field may have positive
characteristic.

## The actual base change

The base map is the actual scheme morphism

`b = Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec K ⟶ Spec k`,

written inline in each statement. This is the same map as the existing
`Langlands.GroupScheme.algebraBaseMap k K`. The functor is the published
`GroupScheme.baseChange b`, defined as `(Over.pullback b).mapGrp`. Thus
`G_K = (GroupScheme.baseChange b).obj G` is the fibre product
`G ×_{Spec k} Spec K` over `Spec K` with the pulled-back group law. For a
homomorphism `π : C ⟶ G` of `k`-groups, `π_K = (GroupScheme.baseChange b).map π`
is the pulled-back actual morphism `C_K ⟶ G_K`. No other model of the base
change is used.

## The components

- `IsSemisimpleFieldExtensionStatement`: if `IsSemisimple G` for an actual
  group scheme `G` over `Spec k`, then `IsSemisimple G_K`.
- `IsSimplyConnectedFieldExtensionStatement`: if `IsSimplyConnected G`, then
  `IsSimplyConnected G_K`.
- `IsSimplyConnectedCoverFieldExtensionStatement`: for all `k`-groups `C`, `G`
  and every homomorphism `π : C ⟶ G`, if `IsSimplyConnectedCover π`, then
  `IsSimplyConnectedCover π_K`.
- `SimplyConnectedFieldExtensionStatement` is the conjunction of these three
  components at the same universe `u`.

Each component states only the direction from `k` to `K`. It does not claim
that the property descends from `K` to `k`. The cover component quantifies
over every supplied map `π`. It does not refer to a cover chosen by an
existence theorem, and it assumes no existence, lifting or base-change law.

The semisimplicity component is included because the Library had no exact
field-extension statement or theorem for `IsSemisimple`. Both other
conclusions contain it, through `IsSimplyConnected.isSemisimple` and
`IsSimplyConnectedCover.isSemisimple`.

## Meaning of the conclusions over `K`

All predicates are the published ones, unchanged.

- `IsSemisimple G_K` means two things. First, `G_K` is connected reductive:
  smooth, affine and connected over `Spec K`, with trivial unipotent radical
  after base change to an algebraic closure of `K`. Second, `G_K` has finite
  centre: some actual closed subgroup `Z ⟶ G_K` represents the full
  scheme-theoretic centre functor, and `Z` is finite over `Spec K`. The centre
  is tested on all schemes over `Spec K`, including nonreduced ones, so the
  representative keeps its nilpotents.
- `IsSimplyConnected G_K` means `G_K` is semisimple and every central isogeny
  `H ⟶ G_K` from a semisimple group `H` over `K` is an isomorphism. Here `H`
  ranges over all such `K`-groups, not only base changes of `k`-groups.
- `IsSimplyConnectedCover π_K` has four parts. The target `G_K` is semisimple,
  the source `C_K` is simply connected, and `π_K` is a central isogeny. The
  fourth part is the universal property `HasCentralCoverUniversalProperty π_K`
  over `K`: every central isogeny `q : H ⟶ G_K` from a semisimple `K`-group `H`
  has a unique homomorphism `a : C_K ⟶ H` with `a ≫ q = π_K`.
- The central isogeny predicate `IsCentralIsogeny` asks for an isogeny that
  is finite, flat and surjective, with locally finitely presented underlying
  morphism. Its actual kernel inclusion must be central. The kernel is the
  full scheme-theoretic one: the Library `kernel π_K` is the pullback of
  `π_K` along the unit section of `G_K`, with inclusion `kernelι π_K`. Its
  centrality is tested on every scheme over `Spec K`, including nonreduced
  ones, so non-smooth kernels such as `μ_p` in characteristic `p` count. No
  reduced or smooth kernel is substituted.

`IsSimplyConnected` and `IsSimplyConnectedCover` are defined only for group
schemes over `Spec` of a field. This module does not claim that they make
sense over a general base scheme. Base change of central isogenies along
arbitrary scheme morphisms is a separate statement with its own successor.
Proofs may reuse the existing `kernelBaseChangeIso` from
`Langlands.AbelianScheme.KernelBaseChange` to compare kernels with base
change.

## Comparing two covers over `K`

The cover component does not assume that an arbitrary `K`-cover descends to
`k`, and it does not imply such descent. Suppose `h` proves the cover component,
`hπ : IsSimplyConnectedCover π` holds over `k`, and `π' : C' ⟶ G_K` is any
supplied cover over `K` with `hπ' : IsSimplyConnectedCover π'`. Then
`h k K C G π hπ` is a proof of `IsSimplyConnectedCover π_K`. The published
canonical isomorphism `IsSimplyConnectedCover.iso` applied to it and `hπ'`
gives `C_K ≅ C'`, compatible with the maps to `G_K` by `iso_hom_comp`.
By `iso_unique`, it is the only isomorphism compatible with those maps.
This module explains that consequence. It constructs no second isomorphism
and declares no comparison of its own.

## Sources and provenance

All three components are derived. Each specializes a source result to the
Library's exact predicates.

- CGP, *Pseudo-reductive groups*, second edition (2015), source
  `conrad-gabber-prasad-2015-pseudo-reductive`. The definition of simply
  connected semisimple groups is the paragraph just before Corollary A.4.11,
  printed p.500 (PDF p.526). Corollary A.4.11(1), printed pp.500-501
  (PDF pp.526-527), gives a central isogeny `π : G̃ → G` from a simply
  connected semisimple group, unique up to unique isomorphism, and says "its
  formation commutes with any extension of the base field". The cover
  component states this compatibility for every supplied cover. The simple
  connectedness component is its case of a group that is its own cover
  (`π` the identity). No retained project CGP errata was found.
- Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`.
  Proposition 19.13, printed p.400 (PDF p.416), says a group variety is
  reductive if and only if its base change to an extension field is.
  Proposition 19.10 on the same page characterizes semisimple reductive
  groups by finiteness of the centre `Z(G)`. These two give the semisimplicity
  component under the Library's finite-centre convention. Proposition 19.15,
  printed pp.400-401 (PDF pp.416-417), is the central-isogeny criterion used
  by `IsSimplyConnected`. Proposition 18.8, printed p.389 (PDF p.405), is the
  source of the universal property.
- Milne errata, official snapshot of 2026-11-02, source
  `milne-2017-algebraic-groups-errata-2026-11-02`, read in full. Its only
  relevant entry corrects Proposition 18.8 so that the factorization lands in
  the source of the incoming cover, as in `HasCentralCoverUniversalProperty`.
  It does not correct Propositions 19.10, 19.13 or 19.15.

The universal property over `K` is part of the published cover interface, not
a separate source theorem. The cover component therefore packages CGP's
field-extension compatibility together with that unique-factorization law.
Proving it requires showing that `π_K` satisfies the law for every central
isogeny into `G_K`. That is a proof obligation of the successor, not a
hypothesis of this statement.
