# Base change of lines along a field extension

This module serves the proof of `MaximalSplitSubgroupStatement` (Borel–Tits 1965, Théorème 7.2),
`maximalSplitSubgroup` in `MaximalSplitSubgroupProof`. Its parts B0–B6 move the lines of the
generated subgroup from `k` to an extension `K`, such as an algebraic closure, where the
reductivity argument runs.

This is a technical module with no counterpart in the literature. Nothing in it uses
reductivity, maximality or smoothness. `G` is an arbitrary group scheme over `Spec k` and `T` an
arbitrary commutative group scheme over `Spec k`.

## Setting

Throughout, `k` and `K` are fields in the same universe `u` with `[Algebra k K]`.
`bc := algebraBaseMap k K : Spec K ⟶ Spec k` is the base map, and `GroupScheme.baseChange bc`
is the published base-change functor on group schemes. A *line* is a homomorphism
`x : Ga k ⟶ G` from the additive group `Ga k = VectorGroup.groupScheme k 1`.

The statements use the published bijection
`GroupScheme.baseChangePointsEquiv bc G Z` between the points of `G_K` over a `K`-scheme `Z` and
the points of `G` over `Z` regarded as a `k`-scheme (`(Over.map bc).obj Z`). It is multiplicative,
which lets every identity of points over `K` be checked over `k`.
`scalarPoint _ Z c` is the point of `Ga` with coordinate `c ∈ Γ(Z, ⊤)`, and `crd p` is the
coordinate of a point `p` of `Ga`.

## Definition

- `lineBaseChange K x : Ga K ⟶ G_K` (entry definition, B0) is the base change
  `(GroupScheme.baseChange bc).map x`, with its source identified with `Ga K` by the inverse of
  the published `VectorGroup.fieldBaseChangeIso k K 1`. This is the pattern of the published
  `SplitPinning.NormalizedRootParametrization.fieldBaseChangeHom`.

## Results

- `scalarPoint_crd`: every point `p` of `Ga` is `scalarPoint _ Z (crd p)`.
- `baseChangePointsEquiv_lineBaseChange` (B1): for a `K`-scheme `Z` and `c ∈ Γ(Z, ⊤)`,
  `baseChangePointsEquiv bc G Z (scalarPoint _ Z c ≫ lineBaseChange K x)` equals
  `scalarPoint _ ((Over.map bc).obj Z) c ≫ x`. Over `k`, the base-changed line is the original
  line at the same coordinate. `baseChangePointsEquiv_comp_lineBaseChange` is the same statement
  for an arbitrary point `p` of `Ga K`, with `c = crd p`.
- `mono_lineBaseChange` (B2): if the underlying morphism of `x` is a monomorphism, so is that
  of `lineBaseChange K x`. Pullback preserves monomorphisms, and the identification of sources
  is an isomorphism.
- `isTorusEquivariant_lineBaseChange` (B3): if `x` is `T`-equivariant for `t : T ⟶ G` with
  character `a` (`IsTorusEquivariant t x a`), then `lineBaseChange K x` is equivariant for the
  base change of `t`, with the base-changed character `characterLattice.baseChange bc T a`.
  The proof uses the published `RelativeRoot.characterValue_baseChange`.
- `baseChangePointsEquiv_gm`: a unit `u` of `Γ(Z, ⊤)`, viewed as a point of `𝔾_m` over `K` and
  then through the published `Gm.baseChangeIso bc`, corresponds to the same unit viewed as a
  point of `𝔾_m` over `k`.
- `baseChangePointsEquiv_cocharacter`: for `t : T ⟶ G` and a cocharacter `ν`, the value of the
  base change of `t` at the base-changed cocharacter
  `cocharacterLattice.baseChange bc T ν` at a unit `u` corresponds to the value of `t ∘ ν` at `u`
  over `k`. The proof uses the published `cocharacterLattice.groupHom_baseChange`.
- `relationOver_lineBaseChange` (B4): if the rank-one relation `RootCell.RelationOver t ν x y Z`
  of the Library holds for every `k`-scheme `Z`, then
  `RootCell.RelationOver (base change of t) (cocharacterLattice.baseChange bc T ν)
  (lineBaseChange K x) (lineBaseChange K y) Z` holds for every `K`-scheme `Z`. Through
  `baseChangePointsEquiv` the relation over a `K`-scheme `Z` is the relation over `Z` regarded
  as a `k`-scheme, at the same coordinates and the same unit.
- `commute_lineBaseChange` (B5): if `scalarPoint _ Z c ≫ x` and `scalarPoint _ Z d ≫ y`
  commute for every `k`-scheme `Z` and all `c, d`, then for every `K`-scheme `Z`, every point of
  `G_K` over `Z` in the range of `lineBaseChange K x` commutes with every point in the range of
  `lineBaseChange K y`. Ranges are the published `SubgroupFunctor.range`.
- `range_lineBaseChange` (B6): `SubgroupFunctor.range (lineBaseChange K x)` equals
  `SubgroupFunctor.range ((GroupScheme.baseChange bc).map x)`, by the published
  `SubgroupFunctor.range_iso_comp`.

The subgroup of rational points `(SubgroupFunctor.range f).carrier (Over.mk (𝟙 _))` is
`rangePts`, defined in `MaximalSplitGeneratedCell`. B5 is stated here
for every test scheme `Z` and B6 as an equality of subgroup functors. Both specialize to
`rangePts` by taking `Z = Over.mk (𝟙 _)` and by `congrArg`.

## Proof notes

All proofs are short. Each identity of points over `K` is transported by the injective,
multiplicative map `baseChangePointsEquiv bc G Z` to an identity over `k`, and then rewritten
with B1. The private lemma `crd_scalarPoint_aux` (the coordinate of `scalarPoint _ Z c` over `k`
is `c`) matches the hypotheses of `RelationOver` over `k` with those over `K`. The module
imports only Mathlib and published Library modules. It uses no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`, and does not use Borel–Tits 3.22.
