# Double-coset operators for product levels and Hecke operators away from a factor

This internal construction studies the double-coset operators
`[K g L] : V^L → V^K` of `Langlands.Shimura.LevelHecke` for a representation
`ρ : Representation R (H × H') V` of a product of topological groups, over an
arbitrary commutative ring `R`, at product levels `K × K'`. The coset space of
a product level is the product of the coset spaces of the factors. The operator
of `(g, g')` is the composite, in either order, of the operators of `(g, 1)` and
`(1, g')`, so the double-coset operators of the two factors commute. For a
fixed level `K₀` of `H`, the vectors fixed by `K₀ × 1` form a representation of
`H'`. Its `K'`-fixed vectors are the `K₀ × K'`-fixed vectors of `ρ`, and its
double-coset operator `[K' g' L']` is the operator `[K₀ × K' (1, g') K₀ × L']`
of `ρ`. On smooth representations this is a functor to smooth representations
of `H'`, and the identifications are natural. Finally, for a level-trivial
presheaf of modules on the levels of `H × H'`, the published comparison map
from the partial colimit at `K₀` to the colimit over all levels lands in the
`K₀ × 1`-fixed vectors. It intertwines the double-coset operators of `H'` on the
partial colimit with the operators `[K₀ × K' (1, g') K₀ × L']` on the colimit.
All declarations are in namespace `Langlands.Shimura.LevelHecke`.

## Motivation and scope

The final sentence of Proposition 4.10 on printed p. 311 of Harris (1999),
*Galois properties of cohomological automorphic forms on GL(n)*, states that
the spectral sequences of the proposition are `GG(A_f^{ℓ,p})`-equivariant as
the level `K(N)^{ℓ,p}` varies. Only the part of the level away from `ℓ` and
`p` varies there. The published module `Langlands.Shimura.PartialLevelTower`
models this situation group-theoretically for a product `H × H'`, where `H`
carries the fixed level and `H'` the varying level. This module adds the
corresponding double-coset operators: those of `H'` act on the vectors fixed
by a fixed level `K₀` of `H`, and they commute with the operators of `H`.
Harris's passage is motivation only; no statement from it is formalized.

The module does not split any adelic group as a product. It constructs no
Hecke algebra of a product and proves no tensor-product decomposition of Hecke
algebras. It does not prove that the comparison from a partial colimit to
the `K₀ × 1`-fixed vectors of the full colimit is injective or surjective. No
Haar measure or normalization is used.

## Inputs

The published module `Langlands.Shimura.Levels` defines compact open levels
`CompactOpenLevel G` and `heckeLevel K L g`, the level `K ∩ g L g⁻¹`. The
published module `Langlands.Shimura.LevelHecke` provides the following:

- `HeckeCosets K L g`, the finite coset space `K / (K ∩ g L g⁻¹)`;
- `mem_heckeLevel`, stating that `x ∈ heckeLevel K L g` iff `x ∈ K` and
  `g⁻¹ x g ∈ L`;
- `cosetTerm ρ K L g v q = ρ(k g) v` for a coset `q = k (K ∩ g L g⁻¹)`
  (`cosetTerm_mk`);
- `heckeOperator ρ K L g : fixedVectors ρ L →ₗ[R] fixedVectors ρ K`, the sum
  of the coset terms (`heckeOperator_apply`);
- `fixedVectorsFunctor R S` on smooth representations and the natural
  transformation `heckeNatTrans R K L g` with components the operators.

The published module `Langlands.Shimura.PartialLevelTower` defines the product
level `prod K K'` of `H × H'` with open subgroup `K × K'`, and `mem_prod`
states that `x ∈ prod K K'` iff `x.1 ∈ K` and `x.2 ∈ K'`. It also defines the
level functor `withLeft K₀` sending `K'` to `K₀ × K'`, the partial tower
`partialTower K₀ F` (the presheaf `K' ↦ F(K₀ × K')`), its level-triviality
`isLevelTrivial_partialTower`, and the comparison
`reindexComparison (withLeft K₀) F` from the colimit of the partial tower to
the colimit of `F`. The published lemmas `reindexComparison_ι_apply`,
`translate_reindexComparison` and `translate_partialComparison_apply_of_mem`
state that the comparison sends the class of `x` at level `K'` to the class of
`x` at level `K₀ × K'`, that it intertwines translation by `h'` with
translation by `(1, h')`, and that its image is fixed by every `(k, 1)` with
`k ∈ K₀`. The published module `Langlands.Shimura.LevelColimit` provides the
smooth representation `LevelColimit.smoothRep F hF` on the colimit of a
level-trivial presheaf `F` of modules, and `Langlands.Shimura.LevelHecke`
provides the map `levelClass F hF K` from `F(K)` to its `K`-fixed vectors. The published
`fixedVectors ρ S` is the submodule of vectors fixed by a subgroup `S`, and
`fixedVectorsMap` restricts an intertwiner to fixed vectors. The published
`SmoothRep R G` is the full subcategory of Mathlib `Rep R G` of representations
in which every vector is fixed by an open subgroup.

## Trivial coset spaces

For a topological group `G` and levels `K ⊆ L`,
`subsingleton_heckeCosets_one` states that `HeckeCosets K L 1` has at most
one element: any `a, b ∈ K` satisfy `a⁻¹ b ∈ K ∩ L`. The instance for
`HeckeCosets K K 1` is the case `L = K`.

## Cosets of product levels

Let `H : Type v` and `H' : Type v'` be topological groups, `K L` levels of `H`,
`K' L'` levels of `H'`, `g : H` and `g' : H'`.

- `mem_heckeLevel_prod` states that `x` lies in the level
  `heckeLevel (K × K') (L × L') (g, g')` iff `x.1 ∈ heckeLevel K L g` and
  `x.2 ∈ heckeLevel K' L' g'`. Multiplication and inversion in `H × H'` are
  componentwise.
- `prodMk K K' k k'` is the element `(k, k')` of `K × K'` (`coe_prodMk`), and
  `prodSplit K K' k` is the pair of components of an element `k` of `K × K'`.
- `heckeCosetsProdFun` sends the coset of `k` to the pair of cosets of its
  components. It is well defined by `mem_heckeLevel_prod`.
  `heckeCosetsProdFun_injective` and `heckeCosetsProdFun_surjective` prove that
  it is bijective.
- `heckeCosetsProd K L g K' L' g'` is the resulting equivalence
  `HeckeCosets (K × K') (L × L') (g, g') ≃ HeckeCosets K L g × HeckeCosets K' L' g'`.
  `heckeCosetsProd_mk` evaluates it on the coset of `k` by `rfl`, and
  `heckeCosetsProd_symm_mk` states that its inverse sends the pair of cosets
  of `k` and `k'` to the coset of `(k, k')`.
- `card_heckeCosets_prod` states that the number of cosets for the product is
  the product of the numbers of cosets of the factors.

## Operators for product levels

Let `R : Type t` be a commutative ring, `V : Type w` an `R`-module and
`ρ : Representation R (H × H') V`; the representation need not be smooth. Let
`v` be fixed by `L × L'`.

- `cosetTerm_prod_symm_mk` evaluates the coset term of the coset of `(k, k')`
  as `ρ(k g, k' g') v`.
- `heckeOperator_prod_apply` writes `[K × K' (g, g') L × L'] v` as the double
  sum, over `q ∈ HeckeCosets K L g` and `q' ∈ HeckeCosets K' L' g'`, of the
  coset terms of the cosets corresponding to `(q, q')`. The proof reindexes the
  defining sum along `heckeCosetsProd` and uses `Fintype.sum_prod_type`.
- `heckeOperator_prod_apply_out` gives the same sum in terms of chosen
  representatives: `∑_{q, q'} ρ(q.out g, q'.out g') v`.
- `heckeOperator_prod_eq_left_comp_right` states
  `[K × K' (g, g') L × L'] = [K × K' (g, 1) L × K'] ∘ [L × K' (1, g') L × L']`.
  In both operators on the right one factor has the trivial coset space
  `HeckeCosets K' K' 1` or `HeckeCosets L L 1`. Their composite is therefore
  `∑_{a, a'} ρ(a g, 1) ρ(1, a' g') v = ∑_{a, a'} ρ(a g, a' g') v`.
- `heckeOperator_prod_eq_right_comp_left` states the other order:
  `[K × K' (g, g') L × L'] = [K × K' (1, g') K × L'] ∘ [K × L' (g, 1) L × L']`.
  The proof is the same, with the two sums exchanged by `Finset.sum_comm`.
- `heckeOperator_left_comp_right_comm` combines the two:
  `[K × K' (g, 1) L × K'] ∘ [L × K' (1, g') L × L']` equals
  `[K × K' (1, g') K × L'] ∘ [K × L' (g, 1) L × L']` as linear maps
  `V^{L × L'} → V^{K × K'}`.

## The representation away from a fixed level

Let `S` be a subgroup of `H`, and write `S × 1` for the Mathlib subgroup
`S.prod ⊥` of `H × H'`.

- `map_inr_mem_fixedVectors` states that `ρ(1, h')` preserves the vectors
  fixed by `S × 1`, since `(1, h')` commutes with every element `(s, 1)`.
- `awayRep ρ S : Representation R H' (fixedVectors ρ (S.prod ⊥))` is the
  representation `h' ↦ ρ(1, h')` restricted to these vectors
  (`coe_awayRep_apply`).
- `isSmooth_awayRep` states that `awayRep ρ S` is smooth if `ρ` is. If an open
  subgroup `U` of `H × H'` fixes `v`, then the open subgroup of `H'` that is the
  preimage of `U` under `h' ↦ (1, h')` fixes `v` in `awayRep ρ S`.
- For an intertwiner `f` from `ρ` to `σ`, `awayMap f S` is the restriction of
  `f` to the vectors fixed by `S × 1`, as an intertwiner from `awayRep ρ S` to
  `awayRep σ S` (`coe_awayMap_apply`).

Now let `K₀` be a level of `H`.

- `awayFixedEquiv ρ K₀ K'` is the `R`-linear equivalence from the `K'`-fixed
  vectors of `awayRep ρ K₀` to the `K₀ × K'`-fixed vectors of `ρ`. Both
  directions are the identity on underlying vectors
  (`coe_awayFixedEquiv_apply`, `coe_awayFixedEquiv_symm_apply`). A vector
  fixed by `K₀ × 1` and by `1 × K'` is fixed by `K₀ × K'`, since
  `(k, k') = (k, 1)(1, k')`. Conversely a vector fixed by `K₀ × K'` is fixed by
  `K₀ × 1` and by `1 × K'`.
- `awayFixedEquiv_heckeOperator` states that `awayFixedEquiv` carries the
  operator `[K' g' L']` of `awayRep ρ K₀` to the operator
  `[K₀ × K' (1, g') K₀ × L']` of `ρ`. The coset space of the first factor is the
  trivial `HeckeCosets K₀ K₀ 1`. Both operators send `v` to
  `∑_{a'} ρ(1, a' g') v`. `awayFixedEquiv_comp_heckeOperator` states this as an
  equation of linear maps.

## Smooth representations

- `awayFunctor R K₀ : SmoothRep R (H × H') ⥤ SmoothRep R H'` sends `A` to
  `awayRep` of its representation at `K₀`, with smoothness by
  `isSmooth_awayRep`, and a morphism to `awayMap` of its intertwiner.
  `awayFunctor_obj_representation` records the representation by `rfl`.
  The carrier universe `w` is unchanged.
- `awayFixedIso R K₀ K'` is the natural isomorphism
  `awayFunctor R K₀ ⋙ fixedVectorsFunctor R K' ≅ fixedVectorsFunctor R (K₀ × K')`
  with components `awayFixedEquiv` (`awayFixedIso_hom_app`).
- `awayFixedIso_heckeNatTrans` states that `awayFixedIso` intertwines the
  whiskered natural transformation `heckeNatTrans R K' L' g'` with
  `heckeNatTrans R (K₀ × K') (K₀ × L') (1, g')`.

## Partial colimits

Let `F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ ModuleCat R` be level-trivial, with
colimits over the ordered levels of `H'` and of `H × H'`, and assume that `H'`
has a compact open level. Let `K₀` be a level of `H`.

- `reindexComparison_withLeft_apply_mem` states that the comparison
  `reindexComparison (withLeft K₀) F` takes values in the vectors of
  `LevelColimit.smoothRep F hF` fixed by `K₀ × 1`. An element of `K₀ × 1` has
  the form `(k, 1)` with `k ∈ K₀`, so this is
  `translate_partialComparison_apply_of_mem`.
- `partialAwayMap F hF K₀` is this comparison, with restricted codomain, as an
  intertwiner from the smooth representation of `H'` on the partial colimit to
  `awayRep` of `LevelColimit.smoothRep F hF` at `K₀`
  (`coe_partialAwayMap_apply`). It is `H'`-equivariant by
  `translate_reindexComparison`, since `(1, h')` is the image of `h'`.
  `partialAwayHom F hF K₀` is the same map as a morphism of smooth
  representations of `H'` into `(awayFunctor R K₀).obj (LevelColimit.smoothRep F hF)`.
- `awayFixedEquiv_partialAwayMap_levelClass` states that, after
  `fixedVectorsMap` and `awayFixedEquiv`, the class of `x ∈ F(K₀ × K')` at level
  `K'` of the partial tower goes to `levelClass F hF (K₀ × K') x`.
- `awayFixedEquiv_partialAwayMap_heckeOperator` states that, after
  `fixedVectorsMap` and `awayFixedEquiv`, the operator `[K' g' L']` on the
  `L'`-fixed vectors of the partial colimit corresponds to the operator
  `[K₀ × K' (1, g') K₀ × L']` on the colimit of `F`. The proof combines the
  published compatibility of double-coset operators with intertwiners and
  `awayFixedEquiv_heckeOperator`.

## Provenance

This is an internal construction from Mathlib's `QuotientGroup.induction_on`,
`QuotientGroup.eq`, `QuotientGroup.out_eq'`, `Subgroup.mem_subgroupOf`,
`Subgroup.prod`, `Equiv.ofBijective`, `Equiv.sum_comp`,
`Fintype.sum_prod_type`, `Fintype.sum_subsingleton`, `Finset.sum_comm`,
`LinearMap.restrict`, `OpenSubgroup.comap`,
`LinearMap.intertwiningMap_of_isIntertwiningMap` and `NatIso.ofComponents`.
It uses the operators, coset spaces and natural transformations of
`Langlands.Shimura.LevelHecke`, the product levels, partial towers and
comparison maps of `Langlands.Shimura.PartialLevelTower`, the published
`LevelColimit.smoothRep`, and the published `fixedVectors`,
`fixedVectorsMap`, `IsSmooth` and `SmoothRep`. No operator, factorization,
commutation or comparison is supplied as input. The factorization of
double-coset operators of a product is a standard elementary fact, proved here
for the unnormalized coset sums.
