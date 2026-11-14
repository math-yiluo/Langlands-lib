# Ordered integral open cells over the maximal unramified integers

Module `Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellProof`,
namespace `Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCell`.
It proves that the ordered multiplication of the actual family of
`OrderedIntegralOpenCellFamily` is an open immersion, for every generic
cocharacter and every pair of injective enumerations of the indivisible roots of
the two signs. All declarations are at an arbitrary universe `u`.

## General ingredients

- `prop_finiteProduct_hom`: a stable property of structure morphisms passes to a
  finite product over `Fin n`, through the published universe reindexing
  `finiteProductUniverseIso` and `prop_pi_hom`.
- `integralCocharacter`: for `A : IntegralSplitTorusData N i` over a domain `R`
  with fraction field `K`, the actual cocharacter of the integral torus whose base
  change, transported along the generic torus isomorphism, is a given
  cocharacter `ν` (published lattice base-change equivalence for split tori).
  `latticePairing_integralCharacter_integralCocharacter` shows it pairs with the
  published `integralCharacter a` exactly as `ν` pairs with `a`.
  `integralCocharacterHom A ν` is its composite with the integral torus inclusion;
  `baseChange_integralCocharacterHom` identifies its generic fibre, followed by the
  generic identification of `N`, with `ν ≫ i`; `integralCocharacterHom_neg`
  identifies the cocharacter of `-ν` with the opposite cocharacter.
- `isRepresentedBy_genericHom_unipotent` and `isRepresentedBy_genericHom_centralizer`:
  the generic fibre of any representative of the integral dynamic unipotent
  subgroup (respectively centralizer) of `integralCocharacterHom A ν`, followed by
  the generic identification, represents the dynamic unipotent subgroup
  (respectively centralizer) of `ν ≫ i` over `K` (published base-change and
  isomorphism-transport lemmas of the dynamic functors).
- `isIso_orderedMultiplication_of_generic`: over a strictly Henselian discrete
  valuation ring, let smooth affine integral factors `f r` map into a smooth affine
  representative `U` of an integral subgroup functor. Assume that their generic
  fibres represent functors `FK r`, that the generic fibre of `U` represents `VK`,
  that every point of `VK` on every `K`-test scheme is uniquely an ordered product
  of points of the `FK r`, that factors of an integral ordered product are
  integral, and that integral points of each `FK r` lift to integral sections of
  the factor. Then the internal ordered multiplication into `U` is an isomorphism.
  The proof applies the integral-point criterion of
  `IntegralPointIsoCriterion`: the generic fibre is an isomorphism by
  `orderedMultiplication_baseChange` and `isIso_orderedMultiplication_factorHom_iff`,
  and an integral section of `U` lifts because its generic point decomposes, the
  factors are integral and lift, and integral sections of `N` are determined by
  their generic points (`integralPointMap_injective`).
- `isIso_factorHom_of_generic`: for closed integral subgroups `j₁`, `j₂` of `N` with
  `range j₁` inside the functor represented by `j₂`, `Z₂` flat, and generic fibres
  representing the same functor, the factorization of `j₁` through `j₂` is an
  isomorphism. It is a closed immersion with generic isomorphism into a flat
  scheme (`isIso_of_isClosedImmersion_of_isIso_pullback`).
- `splitHom` (an isomorphism), `orderedMultiplication_eq_split` and
  `isOpenImmersion_orderedMultiplication_of_split`: over any base, the ordered
  product indexed by `Fin (n₁ + (n₂ + 1))` is the composite of the canonical
  splitting of the finite product into negative block, middle factor and positive
  block, the product of block maps, and the published triple multiplication
  `Dynamic.tripleCellMultiplication`. If the blocks map isomorphically onto
  representatives of the opposite and positive dynamic unipotent subgroups of a
  cocharacter `χ` of a smooth affine group, and the middle factor maps by an open
  immersion into a representative of its centralizer, the ordered multiplication is
  an open immersion: the published
  `Dynamic.isOpenImmersion_tripleCellMultiplication_overBase` gives the triple
  cell, and products of open immersions over the base are open immersions
  (`Over.tensorHom_left`, `Scheme.pullback_map_isOpenImmersion`).

## The unramified family

With `F`, `K`, `O`, `C`, `E`, `Ω` and `N` as in `OrderedIntegralOpenCellFamily`,
`N` smooth with the zero-fixer point equation `hpts`, and `T` an integral split
torus of `N` with generic torus `C.i`:

- `mem_integralPoints_of_orderedProduct`: for a generic cocharacter and an
  injective enumeration of its indivisible positive roots, ordered factors of an
  integral ordered product of actual root points are integral. The product fixes
  the image of every point of `Ω`; the axiom-free
  `mem_filtration_of_orderedProduct_smul_apartmentMap_eq` puts every factor in the
  depth-zero filtration at that point, hence in the pointwise fixer; and the
  published root/fixer identities `rootGroupPoints_inf_pointwiseFixer_eq_rootFixer`
  and `rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer` give integrality.
- `existsUnique_orderedDecomposition`: unique ordered decompositions in the generic
  dynamic unipotent subgroup on every `K`-test scheme, from the proved
  `RelativeRoot.dynamicRootOrderedProduct`.
- `rootModelMap_facts`: each actual root model map lies in the dynamic unipotent
  subgroup of any cocharacter positive on its root, has generic fibre representing
  the actual root subgroup, and lifts integral root points.
- `exists_isOpenImmersion_centralizer_factor`: the relative identity component of
  the integral centralizer maps by an open immersion into every representative of
  the dynamic centralizer of a generic integral cocharacter. The integral
  centralizer lies in that centralizer, and its comparison map is an isomorphism by
  `isIso_factorHom_of_generic`, since for generic `ν` both generic fibres represent
  `torusCentralizer C.i` (published `IsSplitTorus.dynamicCentralizer_eq_torusCentralizer`).
  The identity-component inclusion is open.
- `isOpenImmersion_family`: the main theorem. Representatives of the opposite
  unipotent, centralizer and unipotent dynamic subgroups of
  `integralCocharacterHom T ν` come from the proved `dynamicBaseRepresentability`;
  they are smooth (`smooth_representatives`, `smooth_centralizer_overRing`) and
  affine. The prescribed index function sends the negative block to the roots
  `aneg`, the middle index to the torus and the positive block to `apos`. The
  negative and positive block products are isomorphisms by
  `isIso_orderedMultiplication_of_generic` with the three preceding lemmas
  (for `-ν` and `ν`), the torus factor is an open immersion by
  `exists_isOpenImmersion_centralizer_factor`, and the three-block lemma concludes.

## Provenance

This implements Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition 8.3.14(3), printed p. 300 / PDF p. 331, by the route of Theorem 8.2.5
(printed pp. 290–291 / PDF pp. 321–322) and Proposition 8.2.4 (PDF pp. 320–321)
(`kaletha-prasad-2023-bruhat-tits-new-approach`). The dynamic open cell of the
integral model is that of the source. The implementation differs from the source
in two places. The source identifies the integral ordered root products with
`U(±λ)` by Theorem 2.11.15 over both fibres and Lemma 8.2.3; here the special
fibre is avoided: the generic fibre uses the field ordered product theorem, and
integral sections lift by the stabilizer factorization of
`GenericOrderedFixerFactors`, so the integral-point criterion (Lemma 2.10.9) gives
the isomorphism. The source identifies `T⁰` with the centralizer by
Proposition 8.2.4 using connected special fibres of the ambient model; here the
ambient model is an arbitrary smooth model with the prescribed points, and the
torus model is taken to be the identity component of the integral centralizer,
whose open inclusion suffices. The 1 November 2024 corrections
(`kaletha-prasad-2024-corrections`, PDF p. 37) replace the second paragraph of
8.3.6 and the end of the proof of Theorem 8.3.13 and impose perfect residue in
§8.3; they do not change Section 8.2 or Proposition 8.3.14.
