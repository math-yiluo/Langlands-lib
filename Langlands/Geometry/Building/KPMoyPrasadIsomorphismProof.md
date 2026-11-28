# Proof: the supplied-data Moy–Prasad isomorphism (KP Theorem 13.5.1 (1))

The theorem `Langlands.Geometry.Building.moyPrasadIsomorphismStatement` proves the
published proposition `MoyPrasadIsomorphismStatement.{u}` (module
`Langlands.Geometry.Building.KPMoyPrasadIsomorphismStatement`) at an arbitrary universe `u`.
The supporting lemmas are in the namespace
`Langlands.Geometry.Building.MoyPrasadIsomorphism` of the same module. The general
group-theoretic and lattice-theoretic tools are in
`Langlands.Geometry.Building.MoyPrasadQuotientAssembly`.

## Statement proved

Take a nonarchimedean local field `F`, a group scheme `G` over `F` with `IsAffineHom G.X.hom`,
and supplied `P : ParahoricBuildingData G`, `Zf : P.CentralizerFiltration` and
`L : P.LieFiltrationData`. Assume `P.SatisfiesApartmentAxioms`,
`Zf.SatisfiesFiltrationAxioms` and `Zf.IsDoubleRootCommutatorFriendly`. Fix an apartment
point `x` and `r s : NNReal` with `0 < r ≤ s` and `MoyPrasadAlternative F G r s`. Assume
`Z(F)_r / Z(F)_s ≅ z_r / z_s`, and assume, for every relative root `α` not of the form `2β`,
the isomorphism of the root block
`U_{α,x,r} U_{2α,x,r} / U_{α,x,s} U_{2α,x,s} ≅ (u_{α,x,r} + u_{2α,x,r}) / (u_{α,x,s} + u_{2α,x,s})`.
All isomorphisms are in the sense of `HasMoyPrasadQuotientIso`. Then
`HasMoyPrasadQuotientIso (Zf.moyPrasad x r) (Zf.moyPrasad x s)
(L.lieFiltration x r).toAddSubgroup (L.lieFiltration x s).toAddSubgroup` holds, that is,
`P_{x,r} / P_{x,s} ≅ 𝔤_{x,r} / 𝔤_{x,s}`.

## Outline

The proof follows the assembly sketched in the statement's Markdown and in KP's proof of
Theorem 13.5.1. A generic cocharacter `ν` fixes the two signs of roots. Lists `aneg` and
`apos` enumerate the non-divisible roots of each sign. Let `K` be the product group

```
K = (∏_{j} U_{aneg j, x, r} U_{2·aneg j, x, r}) × Z(F)_r × (∏_{j} U_{apos j, x, r} U_{2·apos j, x, r}),
```

where each block is the Library subgroup `P.filtrationBlockSubgroup hP x r _` (module
`MoyPrasadBlockExchange`). The proof builds two surjective homomorphisms out of `K`:

- `Θ : K →* P_{x,r} / P_{x,s}`, the ordered product of the images of the coordinates;
- `Λ : K →* 𝔤_{x,r} / 𝔤_{x,s}`, the sum of the images of the coordinates under the supplied
  component isomorphisms.

Both kernels consist of the tuples all of whose coordinates have depth `s`. Then
`hasMoyPrasadQuotientIso_of_ker_eq` (module `MoyPrasadQuotientAssembly`) gives the
conclusion. KP's three alternatives enter only through the inequality `s ≤ r + r`.

## The main theorem

`moyPrasadIsomorphismStatement` introduces all data and hypotheses and proceeds as follows.

1. **Roots.** `G` is smooth (`P.isConnectedReductive.smooth`). The relative roots are
   finite (`IsSplitTorus.finite_relativeRoots`), hence so is each
   `RelativeRoot.indivisiblePositiveRoots P.i v`. A generic cocharacter `ν` exists
   (`IsSplitTorus.exists_genericCocharacter`). `Set.Finite.fin_embedding` gives injective
   lists `aneg : Fin nneg → _` and `apos : Fin npos → _` whose ranges are the
   indivisible roots positive on `-ν` and on `ν`.
2. **`s ≤ r + r`.** `le_add_self_of_moyPrasadAlternative` checks this for each alternative.
   Alternatives (1) and (3) contain `s ≤ 2 * r`. In alternative (2),
   `s ≤ r₀ + 2n ≤ 2r₀ + 2n = r + r`, using `r₀ ≥ 0`.
3. **Commutators.** `commutator_moyPrasad_le` (module `MoyPrasadCommutatorGenerators`)
   gives `⁅P_{x,r}, P_{x,r}⁆ ≤ P_{x,r+r}`. This step uses the apartment axioms, the
   filtration axioms and `IsDoubleRootCommutatorFriendly`. Since the Moy–Prasad filtration
   is decreasing (`moyPrasad_antitone`), `⁅P_{x,r}, P_{x,r}⁆ ≤ P_{x,s}`. Hence `P_{x,s}` is
   normal in `P_{x,r}` (`subgroupOf_normal_of_commutator_le`).
4. **The group side.** `exists_moyPrasadQuotient_hom` gives `Θ`.
5. **The components.** The hypothesis on `Z` gives
   `φZ : Z(F)_r →* z_r / z_s`, surjective with kernel `Z(F)_s`. For each `aneg j`, the
   hypothesis on root blocks applies because an indivisible root is not twice a relative
   root (`RelativeRoot.indivisibleRoots`, with multiplier `2`). The hypothesis is stated
   for `Subgroup.closure` of the blocks. `closure_filtrationBlock_eq` rewrites the closure
   as `P.filtrationBlockSubgroup`, at depth `r` and at depth `s`. This gives
   `φN j`, surjective with kernel the depth-`s` block. The same holds for `apos` (`φP j`).
6. **The Lie side.** `exists_lieQuotient_hom`, applied to `φN`, `φZ` and `φP`, gives `Λ`.
7. **Kernels.** For `p ∈ K`, `Θ p = 1` holds iff every coordinate of `p` has depth `s`.
   `Λ p = 1` holds iff every `φN j (p.1 j)`, `φZ p.2.1` and `φP j (p.2.2 j)` is `1`. By the
   kernel descriptions of the components, these two conditions agree coordinatewise.
   So `Θ.ker = Λ.ker`, and `hasMoyPrasadQuotientIso_of_ker_eq` concludes.

## The group side: `exists_moyPrasadQuotient_hom`

Assume `0 < r ≤ s` and `⁅P_{x,r}, P_{x,r}⁆ ≤ P_{x,s}`. Inside the proof, the quotient
`A = P_{x,r} / P_{x,s}` carries the commutative group structure
`quotientCommGroupOfCommutatorLE`.

- Each block `P.filtrationBlockSubgroup hP x r _` lies in `P_{x,r}`
  (`filtrationBlockSubgroup_le_moyPrasad`). An element of the block is `v w` with
  `v ∈ U_{a,x,r}` and `w` in the double filtration. The latter is `U_{2a,x,r}` when `2a` is
  a relative root and trivial otherwise (`doubleFiltration_of_mem`,
  `doubleFiltration_of_not_mem`). Both factors lie in `P_{x,r}` by
  `filtration_le_moyPrasad`. The image `j(Z(F)_r)` lies in `P_{x,r}`
  (`image_le_moyPrasad`).
- `Θ p` is the product in `A` of the images of the negative coordinates, of `j(p.2.1)`,
  and of the positive coordinates. Since `A` is commutative, `Θ` is a homomorphism.
- `Θ p` is the image in `A` of the ordered product
  `Zf.orderedMoyPrasadProduct x r aneg apos` of the coordinates of `p` (module
  `KPMoyPrasadProductStatement`). That product lies in `P_{x,r}` because
  `range_orderedMoyPrasadProduct_eq` (module `MoyPrasadProductCoordinates`) identifies its
  range with `P_{x,r}`. That theorem uses the apartment axioms, commutator friendliness
  (the first component of `SatisfiesFiltrationAxioms`), `0 < r` and the genericity of `ν`.
- **Surjectivity.** Every element of `P_{x,r}` is such an ordered product, again by
  `range_orderedMoyPrasadProduct_eq`.
- **Kernel.** If all coordinates have depth `s`, the ordered product is an ordered product
  at depth `s`, so it lies in `P_{x,s}` by `range_orderedMoyPrasadProduct_eq` at `s`
  (`0 < s` follows from `0 < r ≤ s`). Conversely, suppose the ordered product of `p` lies
  in `P_{x,s}`. Then it is also the ordered product of some tuple `c` at depth `s`. The
  blocks and `Z(F)_t` decrease in `t` (`filtrationBlock_antitone`,
  `CentralizerFiltration.antitone`), so `c` is also a tuple at depth `r`. The ordered
  product at depth `r` is injective (`orderedMoyPrasadProduct_injective`, module
  `MoyPrasadOrderedEmbedding`). So `p` and `c` have the same coordinates, and the
  coordinates of `p` have depth `s`.

## The Lie side

Write `E = GenericLie.equiv 𝒪[F] G` for the identification of `GenericLie 𝒪[F] G` with
`Lie(G)` over `F`, the `F`-vector space `Additive (lieKernel G F)`. `weightSpace P.i χ` is
the weight space of `S` for the character `χ`.

- **Weight spaces of root blocks** (`positiveWeightSpan_nsmul_le`,
  `rootBlockLie_mem_pairWeightSpace`). Under the apartment axioms and for generic `ν`, let
  `a` be a relative root and `m > 0`. A positive multiple `n m a` that is a relative root
  is `a` or `2a` (`root_multiple_eq_one_or_two`, module `ChamberPositiveCollection`). Any
  other positive multiple has weight space `0`: it is nonzero because `ν` is generic
  (`nsmul_ne_zero_of_isGeneric`), and a nonzero character with a nonzero weight space is a
  relative root (`mem_relativeRoots`). Hence `RelativeRoot.positiveWeightSpan P.i (m • a)`
  lies in `𝔤_a + 𝔤_{2a}`. Each `u_{β,x,t}` lies in `P.rootLieSpace β`, the preimage under
  `E` of `positiveWeightSpan P.i β` (`rootLie_le_rootLieSpace`). So for every `t`, `E`
  maps `L.rootBlockLie x a t` into `𝔤_a + 𝔤_{2a}`.
- **The centralizer.** `E` maps the image of `Lie(Z)` under the differential of `j` into
  `weightSpace P.i 0` (`equiv_map_centralizer_mem_weightSpace_zero`, via
  `Lie.mem_weightSpace_zero_of_mem_torusCentralizer`, since `Z` represents the centralizer
  of `S`). The differential `GenericLie.map 𝒪[F] P.centralizer.j` is injective because
  `j` is a monomorphism (`genericLie_map_centralizer_injective`, via
  `Lie.targetMapLinear_injective`).
- **Independence** (`eq_zero_of_sum_pairWeightSpace_eq_zero`). The weight spaces of the
  split torus `S` form an internal direct sum (`isInternal_weightSpace_of_isSplitTorus`).
  The proof groups them along the sets `{0}` and `{a, 2a}` for `a` in the two lists.
  These sets are pairwise disjoint, so the grouped spaces are independent
  (`iSupIndep_biSup_of_pairwise_disjoint`). Disjointness uses four facts. A root and its
  double are nonzero, by genericity. The two lists are injective and of opposite signs on
  `ν`. An indivisible root is not twice a relative root. `2a = 2b` for relative roots
  forces `a = b`, `a = 2b` or `b = 2a` (`root_eq_or_twice_of_common_positive_multiple`,
  module `ApartmentRootRays`). So a sum of vectors, one in each `𝔤_a + 𝔤_{2a}` and one of
  weight `0`, vanishes only if each vector does.
- **Covering** (`exists_eq_or_double_of_mem_relativeRoots`,
  `exists_sum_eq_of_mem_lieFiltration`). Every relative root `b` is `a` or `2a` for some
  `a` in one of the lists. `b` pairs nonzero with `ν`, and
  `exists_indivisiblePositiveRoot_eq_or_double` (module `ChamberPositiveCollection`)
  applies to the sign of the pairing. By `lieFiltration_eq_sup_rootLie`,
  `𝔤_{x,t} = j(z_t) + Σ_α u_{α,x,t}`. Each `u_{α,x,t}` lies in the block of the listed root
  `a` with `α ∈ {a, 2a}` (`rootLie_le_rootBlockLie`). So every element of `𝔤_{x,t}` is a
  sum of one element of each negative block, the image of one element of `z_t`, and one
  element of each positive block, all at depth `t`. The proof is by
  `Submodule.iSup_induction`.
- **Quotient maps.** `rootBlockQuotientMap` and `centralizerQuotientMap` are the maps
  `(u_{a,x,r} + u_{2a,x,r}) / (u_{a,x,s} + u_{2a,x,s}) → 𝔤_{x,r} / 𝔤_{x,s}` and
  `z_r / z_s → 𝔤_{x,r} / 𝔤_{x,s}`. They are induced by the inclusion
  (`rootBlockLie_le_lieFiltration`) and by the differential of `j`
  (`centralizerLieImage_le_lieFiltration`) through `addSubgroupQuotientMap`.
  `sum_quotientMap_mk` computes a sum of their values on classes as the class of the sum.
- **Injectivity on sums** (`eq_zero_of_sum_quotientMap_eq_zero`). Suppose the sum of the
  images of classes `[X_j]`, `[Y]` and `[X'_j]` vanishes. Then the sum of the
  representatives lies in `𝔤_{x,s}`. By covering at depth `s` it equals a sum of block
  elements `W_j`, `W'_j` and the image of some `y ∈ z_s`, all at depth `s`. The differences
  `X_j - W_j`, `X'_j - W'_j` and `j(Y - y)` then sum to `0`. By the weight-space
  statements and independence, each difference is `0`. Injectivity of the differential of
  `j` gives `Y = y`. So every class is `0`.
- **Surjectivity on sums** (`exists_sum_quotientMap_eq`). By covering at depth `r`, every
  class in `𝔤_{x,r} / 𝔤_{x,s}` is such a sum.
- **`Λ`** (`exists_lieQuotient_hom`). Given surjective homomorphisms `φN j`, `φZ`, `φP j`
  from groups onto the block quotients and onto `z_r / z_s`, `Λ` sends a tuple to the sum
  in `𝔤_{x,r} / 𝔤_{x,s}` of the images of its coordinates. It is a homomorphism because
  each `φ` is and the target is abelian. It is surjective by surjectivity on sums and of
  the `φ`. By injectivity on sums, `Λ p = 1` exactly when every coordinate of `p` is in the
  kernel of its `φ`.

## Scope

The building data, the filtration of `Z(F)` and the Lie lattices are supplied, as in the
statement. The proof constructs neither them nor any component isomorphism: the
isomorphisms for `Z` and the root blocks are the statement's hypotheses. No hypothesis is
added to the statement and no unproved proposition is assumed. The proof uses
`Zf.SatisfiesFiltrationAxioms` through `commutator_moyPrasad_le` and through its first
component `IsCommutatorFriendly`. Of the alternatives of KP §13.5, it uses only that each
implies `s ≤ r + r`; the weakly induced torus of alternative (1) is not used. The axioms
reported for the theorem are `propext`, `Classical.choice` and `Quot.sound`.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 13.5.1 and its proof,
printed pp. 474–476 (PDF pp. 505–507). KP prove that the ordered product map from the
product of root-group quotients and the torus quotient to `G(k)_{x,r}/G(k)_{x,s}` is an
isomorphism of abelian groups (via Proposition 13.2.5(3),(4)), and that the Lie algebra
quotient decomposes into the corresponding direct sum. The implemented proof follows this
assembly over `F`, with the component isomorphisms taken from the statement's hypotheses.
