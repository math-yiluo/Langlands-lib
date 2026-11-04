# Connected reductive groups have trivial second centre

Module `Langlands.GroupScheme.Adjoint.SecondCenterReductive`, namespace
`Langlands.GroupScheme.SecondCenter`. The property proved is
`SecondCenterTrivial G` from module `Langlands.GroupScheme.Adjoint.SecondCenter`:
a point `g : T ⟶ G.X` all of whose commutators `(a ≫ g) * h * (a ≫ g)⁻¹ * h⁻¹`
(for every `a : T' ⟶ T` and every `h : T' ⟶ G.X`) lie in `center G` is itself
in `center G`.

## Declarations

*Group theory* (an arbitrary group `Γ` and an element `g` such that every
commutator `x * g * x⁻¹ * g⁻¹` is central):

- `commute_commutator_of_forall_mem_center`: every commutator
  `a * b * a⁻¹ * b⁻¹` commutes with `g`.
- `commute_prod_of_forall_mem_center`: the product of any list of commutators
  commutes with `g`.

*Schemes* (over an arbitrary base `S`):

- `over_ext_of_dominant`: two morphisms `f f' : X ⟶ Y` in `Over S`, with
  `Y.hom` separated, are equal once `j ≫ f = j ≫ f'` for some `j : W ⟶ X` whose
  underlying scheme morphism is scheme-theoretically dominant.
- `isSchemeTheoreticallyDominant_of_appTop_injective`: a morphism to an affine
  scheme that is injective on global sections is scheme-theoretically dominant.
- `isSchemeTheoreticallyDominant_of_epi`: an epimorphism in `Over S` whose target
  has affine underlying scheme has scheme-theoretically dominant underlying
  morphism.
- `isAffineHom_tensor`: the cartesian product in `Over S` of two objects that
  are affine over `S` is affine over `S`.

*Group schemes* (`G : GroupScheme S`):

- `forall_mem_center_of_hyp`: the hypothesis of `SecondCenterTrivial` for `g`,
  restated as: for every `b : Y ⟶ T` and every `x : Y ⟶ G.X`, the commutator
  `x * (b ≫ g) * x⁻¹ * (b ≫ g)⁻¹` lies in the centre of the group `Y ⟶ G.X`.
- `commute_comp`: precomposition preserves commuting pairs of points.
- `comp_commutatorMap_id`: composing a point `x : Y ⟶ G.X ⊗ G.X` with
  `commutatorMap (𝟙 G) (𝟙 G)` gives the commutator of its two coordinates.

*Over a field `k`* (`G : GroupScheme (Spec k)`):

- `commute_inclusion_of_hyp`: let `G` be affine over `Spec k`, let `E` be a
  `GeneratedImage (commutatorMap (𝟙 G) (𝟙 G))` (a closed subgroup representing
  the closed envelope of the commutator map) with
  `E.HasSmoothConnectedGeneration`, and let `g : T ⟶ G.X` satisfy the
  hypothesis of `SecondCenterTrivial`. Then the two points
  `fst ≫ E.inclusion` and `snd ≫ g` of `G` over `E.group.X ⊗ T` commute.
- `commute_of_epi_subgroupProductMap`: let `G` and `Z` be affine over `Spec k`,
  `i : Z ⟶ G` central (`IsCentral i`), `d : D ⟶ G` a derived subgroup
  (`IsDerivedSubgroup d`), and `subgroupProductMap i d` an epimorphism in
  `Over (Spec k)`. If `x ≫ d` commutes with `b ≫ g` for all points `x` of `D`
  and `b : Y ⟶ T`, then `fst` and `snd ≫ g` commute as points of `G` over
  `G.X ⊗ T`.
- `secondCenterTrivial_of_epi_subgroupProductMap`: a smooth, affine group `G`
  over `Spec k` with connected underlying space, having such `i` and `d`, has
  trivial second centre.
- `secondCenterTrivial_of_centralDerivedProduct`: assuming
  `ReductiveCentralDerivedProductStatement.{u}` as the explicit hypothesis
  `hDP`, every connected reductive group `G` over a field `k : Type u` has
  trivial second centre.

## Proof

*Group theory.* The map `x ↦ x g x⁻¹ g⁻¹` is a homomorphism `Γ → Z(Γ)`: the
identity `xy g (xy)⁻¹ g⁻¹ = x (y g y⁻¹ g⁻¹) g x⁻¹ g⁻¹` and centrality of
`y g y⁻¹ g⁻¹` give `c(xy) = c(x) c(y)`. Since its values commute with each
other, it sends `a b a⁻¹ b⁻¹` to `1`, which says that the commutator commutes
with `g`. For lists, the centralizer of `g` is a subgroup, so it contains every
product of commutators.

*Scheme lemmas.* `over_ext_of_dominant` is the Library lemma
`ext_of_isSchemeTheoreticallyDominant` (module
`Langlands.GroupScheme.Dynamic.Uniqueness`) applied to the underlying scheme
morphisms, with the structure morphism of `Y` as the separated test. For an
affine target, scheme-theoretic dominance means that the kernel ideal sheaf is
zero, which for an affine target is the kernel of the map on global sections.
An epimorphism in `Over S` is an epimorphism of schemes (`Over.forget` preserves
epimorphisms), and the Library lemma
`Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi` says it is
injective on global sections. Affineness of the product follows because
`pullback.fst` is affine by base change and affine morphisms compose.

*Commutator subgroup.* In `commute_inclusion_of_hyp`, write
`E.HasSmoothConnectedGeneration` as: `E.group` is smooth and affine over
`Spec k`, and for some `n > 0` the ordered product map
`E.powerMap n : (G × G)ⁿ ⟶ E.group.X` is dominant. A smooth scheme over a field
is reduced (`isReduced_of_smooth_over_field`), so the dominant
`E.powerMap n` is scheme-theoretically dominant (Mathlib's
`IsSchemeTheoreticallyDominant.of_isDominant`); it is quasi-compact since
`(G × G)ⁿ` and `E.group` are affine. Every object over a field is flat, so the Library lemma
`ImageGeneration.isSchemeTheoreticallyDominant_whiskerRight` makes
`E.powerMap n ▷ T` scheme-theoretically dominant. By `over_ext_of_dominant` it
suffices to check commutation after precomposing with this map. There
`fst ≫ E.inclusion` becomes, by `E.powerMap_comp` and `orderedPowerMap_points`,
an ordered product of `n` commutators of points of `G`, while `snd ≫ g` becomes
`snd ≫ g` restricted along the projection to `T`. The group lemma
`commute_prod_of_forall_mem_center` in the group of points over
`(G × G)ⁿ ⊗ T`, with the hypothesis supplied by `forall_mem_center_of_hyp`,
finishes.

*Whole group.* In `commute_of_epi_subgroupProductMap`, the target `G.X` is
affine and `subgroupProductMap i d` is an epimorphism, so it is
scheme-theoretically dominant; it is quasi-compact since `Z × D` and `G` are
affine (`D` is a closed subgroup of the affine `G`). Whiskering by `T` keeps it
scheme-theoretically dominant. After precomposition, `fst` becomes the product
`(z ≫ i) * (x ≫ d)` of a central point and a point of `D`. The first factor
commutes with everything by centrality of `i`, the second commutes with
`snd ≫ g` by hypothesis, so the product commutes.

*Assembly.* In `secondCenterTrivial_of_epi_subgroupProductMap`, take
`E := smoothConnectedCommutatorImage k G` (module
`Langlands.GroupScheme.Derived.ConnectedSmoothness`), which has
`HasSmoothConnectedGeneration`. `E.inclusion` is a derived subgroup
(`GeneratedImage.isDerivedSubgroup`), so it has the same range as `d`; hence
every point `x ≫ d` of `D` is `y ≫ E.inclusion` for a point `y` of `E.group`,
and restricting `commute_inclusion_of_hyp` along `lift y b` shows that it
commutes with `b ≫ g`. Then `commute_of_epi_subgroupProductMap` applies, and
restricting along `lift h a` shows that `a ≫ g` commutes with every `h`, which
is `g ∈ center G`. Finally, `secondCenterTrivial_of_centralDerivedProduct`
takes the central torus `i`, the derived subgroup `d` and the product
epimorphism from `hDP` and uses the smoothness, affineness and connectedness
of a connected reductive group.

## Provenance

This is the group-theoretic half of the proof that the quotient of a connected
reductive group by its centre has trivial centre (Milne, *Algebraic Groups*
(2017), Corollary 17.62(e), printed pp.372–373 / PDF pp.388–389). Milne
argues differently. He takes the inverse image `Z'` of the centre of `G/Z(G)`
in `G`, a normal subgroup of `G`, and applies Corollary 12.41 (printed p.244 /
PDF p.260) with `H = Z'` and `N = Z(G)`. That corollary is an
extension-rigidity result: if `N` is a normal subgroup of an algebraic group
`H` such that `N` and `H/N` are of multiplicative type, then every action of a
connected algebraic group on `H` by group homomorphisms preserving `N` is
trivial. The official errata snapshot of 2026-11-02
(`milne-2017-algebraic-groups-errata-2026-11-02`) adds that `N` must be
central in `H`, which holds for `Z(G)` inside `Z'`. So `G` acts trivially on
`Z'` by conjugation, and `Z' = Z(G)`. In that application the
multiplicative-type hypotheses on `N = Z(G)` and on `H/N`, which is the centre
of the reductive group `G/Z(G)`, come from 17.62(a). The Library has no theory
of groups of multiplicative type, so the route here replaces this argument by
the decomposition of `G` into a central torus and its derived subgroup: the
input `ReductiveCentralDerivedProductStatement` (Milne 2017, Proposition 21.61
with 12.46(b), as recorded in that statement's Markdown) appears only as the
explicit hypothesis `hDP` of `secondCenterTrivial_of_centralDerivedProduct`,
so nothing in this module depends on an unproved statement. The commutator
homomorphism argument is standard elementary group theory; all scheme inputs
are proved Library and Mathlib results.
