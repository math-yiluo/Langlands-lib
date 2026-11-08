# The idele norm and the idele-class norm are open maps

Author: Worker 1805.

This module, in namespace `Langlands.Global.AdelicFunctoriality`, proves that for number
fields `K : Type u` and `L : Type v` with `[Algebra K L]` the actual idele norm
`ideleNorm : 𝕀_L →ₜ* 𝕀_K` of [Norm](Norm.md) and the idele-class norm
`ideleClassNorm : C_L →ₜ* C_K` of [IdeleClassNorm](IdeleClassNorm.md) are open maps. No Galois,
cyclic or ramification hypothesis is needed. The topologies are the existing ones: the units
topology on the actual idele group and the quotient topology on the idele-class group. The
module changes no imported definition and declares no global instance.

## Statements

- `fiberProd P N`: for index types `ι`, `κ`, a relation `P : κ → ι → Prop` with finitely many
  `i` over each `k` (`[∀ k, Fintype {i // P k i}]`), and monoid homomorphisms
  `N k i : G i →* H k` into commutative groups, the homomorphism `(∀ i, G i) →* ∀ k, H k`
  whose `k`-coordinate is `∏ i over k, N k i (x i)` (`fiberProd_apply`).
- `nhds_one_le_map_fiberProd`: `𝓝 1 ≤ map (fiberProd P N) (𝓝 1)` in the product topologies,
  provided every `i` lies over at most one `k`; each `k` has a chosen `s k` over it; the map
  `N k (s k)` sends every neighbourhood of `1` to a neighbourhood of `1`; and `N k (s k)` is
  surjective for all but finitely many `k`.
- `image_pow_mem_nhds_one (hn : n ≠ 0)`: over a complete nontrivially normed field of
  characteristic zero, the `n`-th power map on units sends every neighbourhood of `1` to a
  neighbourhood of `1`.
- `image_finiteLocalNorm_mem_nhds p q` and `image_infiniteLocalNorm_mem_nhds p q`: for a
  finite place `q` of `L` over `p` (`[q.asIdeal.LiesOver p.asIdeal]`), respectively an
  infinite place `q` over `p` (`[q.LiesOver p]`), the local norm on units
  `Units.map (localNorm p q)` sends every neighbourhood of `1` to a neighbourhood of `1`.
  [LocalNormNeighborhood](LocalNormNeighborhood.md) proves this only for the whole unit group
  (its image, the range, is a neighbourhood of `1`). The openness argument needs it for every
  neighbourhood.
- `nhds_one_le_map_of_comm`: if `e' ∘ f = f' ∘ e` for isomorphisms `e`, `e'` of topological
  groups and `𝓝 1 ≤ map f' (𝓝 1)`, then `𝓝 1 ≤ map f (𝓝 1)`.
- Infinite part: `infiniteLocalUnitNorm p q` is `Units.map (InfiniteExtension.localNorm p q)`.
  `infiniteUnitNorm K L` is the `fiberProd` of these maps over the relation "`q` lies over
  `p`", from `∀ q : InfinitePlace L, q.Completionˣ` to `∀ p : InfinitePlace K, p.Completionˣ`.
  `nhds_one_le_map_infiniteUnitNorm` and `nhds_one_le_map_infiniteAdeleNorm` state
  `𝓝 1 ≤ map f (𝓝 1)` for `f = infiniteUnitNorm K L` and for
  `f = Units.map infiniteAdeleNorm` on `(InfiniteAdeleRing L)ˣ`.
- Finite part: the `S = ∅` product model of
  [SUnitIdeleTopology](../Arithmetic/SUnitIdeleTopology.md), `model F ∅`, is
  `(InfiniteAdeles F)ˣ` times the product over finite places `w` of the valuation units
  `localFactor F ∅ w`. `valued_eq_one_iff_mem_units` identifies valuation-one units with units
  of the valuation ring. `localFactor_empty_mem_nhds` shows that `localFactor F ∅ w` is a
  neighbourhood of `1`. `localNorm_mem_localFactor_empty` shows that the local norm keeps
  valuation units. `localFactorNorm p q` is the local norm restricted to the valuation units.
  `image_localFactorNorm_mem_nhds` is the neighbourhood statement for it.
  `eventually_localFactorNorm_surjective` states that for all but finitely many `p`,
  `localFactorNorm p (placeAbove L p)` is surjective, where `placeAbove` is the chosen place
  above `p` of [LocalDegree](LocalDegree.md).
- `finiteModelNorm K L : finiteModel L ∅ →* finiteModel K ∅` is the `fiberProd` of the
  `localFactorNorm`. `modelNorm K L : model L ∅ →* model K ∅` is
  `(Units.map infiniteAdeleNorm).prodMap (finiteModelNorm K L)`.
- `ideleNorm_assemble`: `ideleNorm (assemble L ∅ x) = assemble K ∅ (modelNorm K L x)`.
- `nhds_one_le_map_modelNorm`: `𝓝 1 ≤ map (modelNorm K L) (𝓝 1)`.
- `isOpenEmbedding_assemble F`: `assemble F ∅ : model F ∅ →* 𝕀_F` is an open embedding.
- `isOpenMap_ideleNorm : IsOpenMap (ideleNorm (K := K) (L := L))`.
- `isOpenMap_ideleClassNorm : IsOpenMap (ideleClassNorm (K := K) (L := L))`.

## Proofs

`nhds_one_le_map_fiberProd`: a basic neighbourhood of `1` in the target product constrains
finitely many coordinates `I` by neighbourhoods `t i`. Let `J` be the finite set of `k` that
lie under some `i ∈ I`, together with the finitely many `k` where `N k (s k)` is not
surjective. On `J` take the images `N k (s k) '' t (s k)`, which are neighbourhoods of `1` by
hypothesis. Their box `set_pi_mem_nhds` is a neighbourhood of `1` in the target product. Each
`y` in it has a preimage `x`. At `s k` choose a preimage `c` of `y k`, inside `t (s k)` when
`k ∈ J` and arbitrary otherwise (possible by surjectivity off `J`). At every other index put
`1`. Since every `i` lies over at most one `k`, the `k`-coordinate of `fiberProd P N x` is
the single factor `N k (s k) c = y k` (`Finset.prod_eq_single`). The coordinates in `I` are
in `t i`: either `i = s k` with `k ∈ J`, or the value is `1`.

`image_pow_mem_nhds_one`: the inverse function theorem `HasStrictDerivAt.map_nhds_eq` for
`x ↦ x ^ n` at `1`, whose derivative `n` is nonzero. Given a neighbourhood `W` of `1` in units,
choose a neighbourhood `W'` in the field with `Units.val ⁻¹' W' ⊆ W`. The image of
`W' ∩ {x ≠ 0}` is a neighbourhood of `1`, and its preimage in units consists of `n`-th powers
of elements of `W`. The local statements follow as in
[LocalNormNeighborhood](LocalNormNeighborhood.md): they use the same nontrivially normed field
structures, and `localNorm p q (completionMap p q x) = x ^ d` with `d` the positive local
degree. Pull `t` back along the continuous map `Units.map completionMap`. Its `d`-th powers form
a neighbourhood of `1` and are norms of elements of `t`.

Infinite part: `ContinuousMulEquiv.piUnits` identifies `(InfiniteAdeleRing F)ˣ` with
`∀ w, w.Completionˣ`, and under it `Units.map infiniteAdeleNorm` becomes `infiniteUnitNorm`
(`Units.coe_prod`). `nhds_one_le_map_fiberProd` applies. An infinite place of `L` lies over
only its restriction (`InfinitePlace.LiesOver.comap_eq`). Every `p` has a place above it
(`InfinitePlace.comap_surjective`). The neighbourhood condition is
`image_infiniteLocalNorm_mem_nhds`. Surjectivity is needed only off a finite set, and there
are finitely many infinite places. Openness then transfers by `nhds_one_le_map_of_comm`.

Finite part: a finite place `q` of `L` lies over exactly `q.under (𝓞 K)`
(`finitePlacesAbove_under`). The neighbourhood condition comes from
`image_finiteLocalNorm_mem_nhds`. A neighbourhood of `1` in the subgroup of valuation units has
the form `u ∩ localFactor` with `u` a neighbourhood in the units, and `localFactor` is itself
a neighbourhood: it contains the units of the open valuation subring
(`Submonoid.isOpen_units`, `Valued.isOpen_valuationSubring`). For all but finitely many `p`,
every place above `p` has ramification index one (`eventually_ramificationIdx_eq_one`). There
every valuation unit of `K_p` is the norm of a valuation unit of `L_q`
(`FiniteExtension.exists_localNorm_eq_of_ramificationIdx_eq_one`), which is the surjectivity
condition. `nhds_one_le_map_modelNorm` combines both parts through `nhds_prod_eq` and
`Filter.prod_map_map_eq'`.

`ideleNorm_assemble` is checked coordinatewise: the infinite component agrees by definition,
and every finite component is the product of local norms (`SubmonoidClass.coe_finsetProd`,
`Units.coe_prod`). `isOpenEmbedding_assemble`: `assemble F ∅` is the inclusion of the open
subgroup `sUnitIdeles F ∅` (`isOpen_sUnitIdeles`) composed with the homeomorphism
`productEquiv F ∅`.

`isOpenMap_ideleNorm`: by `IsTopologicalGroup.isOpenMap_iff_nhds_one` it suffices that
`𝓝 1 ≤ map ideleNorm (𝓝 1)`. The open embeddings give `map (assemble F ∅) (𝓝 1) = 𝓝 1`, and
`ideleNorm_assemble` turns `nhds_one_le_map_modelNorm` into this inequality.
`isOpenMap_ideleClassNorm`: the image of an open set `U` of `C_L` is the image under the open
quotient map `𝕀_K → C_K` (`QuotientGroup.isOpenMap_coe`) of the `ideleNorm`-image of the
preimage of `U` in `𝕀_L`. That preimage is open because the quotient map is continuous.

## Provenance

Derived. The local input is the remark in Artin and Tate, *Class Field Theory* (2009),
Chapter VI §3, footnote 2, printed p.25 (PDF p.34): the local norm group `N_p K_p^*` is open
because it contains an open subgroup of the units. The same page uses the fact that at an
unramified prime every unit is a local norm (proof of Lemma 2). The global statement follows
from these two facts and the restricted-product topology of the ideles. It is the standard
openness of the norm map on ideles and idele classes, which Artin and Tate use without a
separate statement. Here it is proved with the published unramified-unit-norm theorem and the
`S = ∅` product model of the idele topology. The fibre-product lemma, the transport lemma and
the model norms are internal packaging. The module was written for task 33286360 (factoring
continuous characters through the transfer), coordinated with its executor, under task
cc3ec74b.
