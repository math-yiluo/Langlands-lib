# Wild inertia inside the inertia of the Weil group

For a p-adic field `K`, this module relates the Library's wild inertia
`weilWildInertia K` (the preimage in the local Weil group of the absolute wild
inertia `Ramification.Padic.wildInertia K`, the closure of the union of the
absolute upper ramification groups of positive index) to the inertia subgroup
`localInertia K` of the Weil group and to the finite Galois subextensions of
the fixed algebraic closure. It establishes the structure used by the
abstract Clifford theory of `Langlands.Representation.Clifford`: inertia `I`
is compact, wild inertia `P` is closed in it, `I / P` is abelian, every open
subgroup of `I` containing `P` is normal with cyclic quotient of index prime to
`p`, and
`P` is pro-`p`. These are the classical facts of J.-P. Serre, *Local Fields*
(1979), registered as `serre-1979-local-fields`, IV §2, Proposition 7 and its
Corollaries 1–4 (printed pp. 67–68, PDF pp. 74–75), transported to the
profinite inertia group through the finite Galois quotients.

## Notation

- `FG K` is the type of finite Galois subextensions `L` of the algebraic
  closure of `K`; `finT K L` is the canonical topological data of the
  corresponding p-adic field `absoluteFiniteExtension K L`, and `res K L` is
  the published restriction `weilInertiaRestriction K L` from Weil inertia
  onto the inertia subgroup of `Gal(L/K)` (`res_coe`; surjective by
  `res_surjective`, the published `weilInertiaRestriction_surjective`).
- `wildIn K` is `weilWildInertia K` regarded as a subgroup of
  `localInertia K`; this uses `weilWildInertia_le_localInertia`, which follows
  from `wildInertia_le_absoluteInertia`: each positive upper group lies in the
  absolute inertia group, which is closed.

## Finite levels

- `iSup_upper_eq_lower_one`: for the ramification groups of a p-adic field `L`
  (with topological data `T`) over a subfield `F`, the supremum of the upper
  ramification groups of positive index is the first lower group.
  Each `G^v` with `v > 0` is `G_{ψ(v)}` with `ψ(v) > 0`, so it lies in `G_1`;
  conversely `G_1 = G^{φ(1)}` with `φ(1) > 0`.
- `map_wildIn`: the image of wild inertia under `res K L` is the first lower
  group, as a subgroup of inertia (`inertiaLowerGroup_eq_map` is the same
  equality for the Library's `inertiaLowerGroup`). The image of absolute wild
  inertia is the image of the union of positive upper groups, by the published
  `absoluteUpperClosedRightImage` at `v = 0`, and every element of absolute
  wild inertia lies in absolute inertia and so comes from Weil inertia
  (`localInertiaEquiv`).
- `exists_res_ker_subset` and `ker_res_le`: every neighbourhood of one in Weil
  inertia contains the kernel of some `res K L`. This is the Krull topology
  (`InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois`): a
  neighbourhood of one contains the fixing subgroup of a finite Galois
  subextension, which is the kernel of the restriction
  (`IntermediateField.restrictNormalHom_ker`).

## Structure of inertia over wild inertia

- `isClosed_wildIn`: wild inertia is closed, as a preimage of a topological
  closure.
- `coprime_index_of_wildIn_le`: an open subgroup `U ⊇ P` of `I` has index
  prime to `p`. It contains the kernel of some `res K L`, so its index equals
  that of its image, which contains the first lower group; the index of the
  latter in inertia is prime to `p` by the published
  `HerbrandBridge.inertia_quotient_lowerOne_cyclic_coprime`.
- `cyclicOpenQuotients_wildIn`: for such a `U` the powers of one element meet
  every right coset of `U` (so `I / U` is cyclic, `U` being normal by
  `commutatorsIn_wildIn`): a lift `g` of
  a generator of the cyclic finite tame quotient works, since an element
  congruent to a power of `g` modulo the first lower group is congruent to it
  modulo `P · ker (res K L) ⊆ U`.
- `mem_wildIn_of_forall`: an element of inertia whose restriction to every
  finite Galois subextension lies in the first lower group lies in wild
  inertia. If not, closedness gives a neighbourhood `O` of one with
  `y O` disjoint from `P`; for `L` with `ker (res K L) ⊆ O`, writing
  `res y = res n` with `n ∈ P` gives `y⁻¹ n ∈ O` and `y (y⁻¹ n) = n ∈ P`.
- `commutatorsIn_wildIn`: every commutator of inertia lies in wild inertia,
  because at every finite level the quotient by the first lower group is
  cyclic, hence commutative.
- `exists_card_inertiaLowerGroup`: the first lower group of a finite Galois
  extension has `p`-power order, by the published
  `Ramification.Padic.finiteTameInertiaStructure`.
- `pPowerOpen_wildIn`: wild inertia has the property `PPowerOpen p` of the
  module `Langlands.Representation.Clifford.PGroup`: an open subgroup of `P`
  contains the elements of `P` in the kernel of some `res K L`, and the image
  of `P` there is a group of order `p^b`.

## Wild inertia of the Weil group

- `wildEquiv K` is the continuous isomorphism between `wildIn K` and
  `weilWildInertia K` (`Subgroup.subgroupOfEquivOfLe`), with
  `wildEquiv_apply`.
- Instances `compactSpace_localInertia` (from the published
  `localInertia_isCompact`), `compactSpace_wildIn` (a closed subset of a
  compact space) and `compactSpace_weilWildInertia` (through `wildEquiv`).
- `pPowerOpen_weilWildInertia`: `weilWildInertia K` has the `p`-power
  property, by `PPowerOpen.of_continuous`.
