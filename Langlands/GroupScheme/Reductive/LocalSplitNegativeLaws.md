# Laws of the negative cell factors of Weyl families

This module transfers the laws of products of root points from the Weyl family of `G` to that
of `H`, for positive roots of any base, and in particular for the negative roots of a given
base in any order. It imports `Langlands.GroupScheme.Reductive.LocalSplitWeylCommutatorReduction`
and contains no `Prop`-valued statement.

Notation: `orderedProduct v e Z w = v_{e 0}(w 0) ⋯ v_{e (r-1)}(w (r-1))` is the ordered product
of root points along an index family `e`. `PosGood v v' pos Z g h` (module
`LocalSplitCommutatorLaws`) says: `orderedProduct v pos Z w · g` is always an ordered product
along `pos`, and every law `orderedProduct v pos Z w · g = orderedProduct v pos Z z` of `G`
gives `orderedProduct v' pos Z w · h = orderedProduct v' pos Z z` in `H`.
`IsNormalSimpleData` and `WeylConjugationRelations` are as in the imported module and in
`LocalSplitWeylConjugationStatement`.

## Results

- `Langlands.LinearAlgebra.exists_base_isPos_iff_not`: for a finite reduced root datum
  `P : RootDatum J (I → ℤ) (I → ℤ)` and a base `b`, some base `b'` has as positive roots
  exactly the roots that are not positive for `b`.

The remaining results are in namespace `Langlands.GroupScheme.LocalSplitCell`. The setting is
a commutative local ring `R` with groups `G`, `H`, data
`IsNormalSimpleData i P b W u` and `IsNormalSimpleData i' P b W u'`, and
`WeylConjugationRelations P b W u u'`, with `J` finite.

- `posGood_rootPoint_of_base`: let `b'` be any base, `pos` an enumeration of its positive roots
  by increasing `b'`-height and `negb` an enumeration of the other roots. Over every local
  ring `A` over `R`, for every `b'`-positive root `β` and every `x`, the pair
  `(v_β(x), v'_β(x))` of Weyl-family points is `PosGood` for the products along `pos`.
- `PosGood.exists_eq`: a `PosGood` pair `(g, h)` is `(orderedProduct v pos Z w,
  orderedProduct v' pos Z w)` for some common coordinates `w`.
- `negativeLaws`: let `neg` be any index family of non-positive roots of `b`. Over every local
  ring `A` over `R`, for every non-positive root `α`, if
  `orderedProduct v neg Z w · v_α(c) = orderedProduct v neg Z z` holds in `G`, then the same
  holds with `v'` in `H`. Here `v`, `v'` are the Weyl families of `u`, `u'`.

## Proof

**The opposite base.** Let `ν` be a cocharacter with `⟨α, ν⟩ = d · ht_b(α)` (imported
`exists_coPairing_eq_height`, with `d > 0`). The functional `x ↦ -(x ⬝ᵥ ν)` is nonzero on all
roots and positive exactly on the non-positive ones. As in
`Langlands.LinearAlgebra.exists_base_rankTwo`, composing with the polarization of the flipped
datum (`dual_polarization_root_pos_iff`, `dual_polarization_root_ne_zero`) gives a functional
on coroots with the same signs, and the imported `exists_base_isPos_iff` gives the base.

**Positive-good points.** `posGood_rootPoint_of_base` applies the imported `posGood_rootPoint`
to the cell `cellMap i v negb pos`, an open immersion by the imported
`LocalSplitBigCell.isOpenImmersion_cellMap`. Its hypotheses are:
- uniqueness of coordinates, `orderedProduct_pos_injective`;
- existence of products, `exists_orderedProduct_mul_rootPoint_eq_pos`, for a cocharacter `ν'`
  with `⟨α, ν'⟩` a positive multiple of the `b'`-height;
- vanishing of commutator coordinates up to position `k`, `posComm_coord_eq_zero_of_monotone`;
- transfer of commutator laws, `posComm_transfer_of_isUnivComm`, from the common universal
  coordinates of `exists_common_isUnivComm_of_base` (imported) for `b'`.

**Negative laws.** Take `b'` from `exists_base_isPos_iff_not` and enumerate its positive roots
by increasing `b'`-height. Each factor of `orderedProduct v neg Z w` is a `b'`-positive point,
so the product is `PosGood` (imported `PosGood.prod_ofFn`). By `PosGood.exists_eq` it is a
product along the enumeration with the same coordinates in `G` and `H`; the same holds for the
product with coordinates `z`. The law then transfers by `PosGood` of `v_α(c)`.

## Provenance and scope

This is internal derived content toward the Isomorphism Theorem over an arbitrary local
ring. The non-positive roots of a base are the positive roots of the opposite base, so the
negative cell factor is handled like a positive one. The transfer of laws through
commutator relations follows the descending induction of Conrad, *Reductive group schemes*
(2014), proof of Lemma 6.2.3, as implemented in the imported `LocalSplitCommutatorLaws`. The
hypotheses `IsNormalSimpleData` (including rank-one normalization) and
`WeylConjugationRelations` are not proved here.
