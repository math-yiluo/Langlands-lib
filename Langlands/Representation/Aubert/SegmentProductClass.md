# The class of a product of segment socles

Module `Langlands.Representation.Aubert.SegmentProductClass`, namespace
`Langlands.Aubert` (helper lemmas in `Langlands.Aubert.SegmentProductClass`).

This module computes the graded exact-K0 class of an actual product of segment
socles `i(π_1, …, π_r)` as the segment polynomial evaluation of the monomial
`X_{Δ_1} ⋯ X_{Δ_r}`. In the proof of Zelevinsky 1980, Corollary 7.5, the
monomial `π(a)` is the class of the product `<Δ_1> × ⋯ × <Δ_r>`, so there the
identity holds by the definition of the multiplication on `R`. In the Library the
graded ring is built from binary products and the product datum `d.induced` is an
iterated product, so the identity needs the proof below. The statement and proof
are internal; they combine published Library results on segment-product data,
binary products and the graded ring. The surjectivity half of
`Langlands.Aubert.SegmentPolynomialComparisonStatement` uses it.

## Main statement

`gradedInclusion_induced_eq_segmentPolynomialEvaluation F T hx hl d hd hfin`:
let `d : T.SegmentProductDatum n` be a segment-product datum of total rank `n`
(any `n`, including `0`), with segments `Δ_i = d.segments i` and blocks
`π_i = d.blocks i`. Suppose `hd : d.HasSegmentSocles`, that is, every `π_i`
satisfies `T.IsSegmentSocle Δ_i π_i`, and let `hfin` be a proof that
`d.induced` has finite length. Then

`gradedInclusion F T n [d.induced] = segmentPolynomialEvaluation F T hx hl (∏ i, X (d.segments i))`,

where `[d.induced] = GeneralLinear.finiteLengthClass n F.Carrier d.induced hfin`
and the right side is computed in the ring `gradedInductionRing F T hx hl`.

## Helper lemmas (`SegmentProductClass`)

- `isIrreducible_of_isSegmentSocle`: a supplied segment socle is irreducible;
  this is the first component of the socle relation in `T.IsSegmentSocle`.
- `hasFiniteLength_induced`: if `d.HasSegmentSocles`, then `d.induced` has
  finite length, in every rank. For `n = 0`, transport finiteness of
  `T.binaryProductUnit` along `SegmentProductOrderedAssembly.zeroDatumUnitIso`.
  For `n > 0`, apply the Library theorem `irreducibleProductFiniteLength` to the
  irreducible blocks.
- `prod_segments_eq_head_mul_tail`: for a datum with `k + 2` segments, a product
  `∏ i, f (d.segments i)` in a commutative monoid is `f` of the head segment
  (`d.shape.headIndex h`) times the product over the segments of
  `SegmentProductSplit.tail d h`. After destructuring `d` this is
  `Fin.prod_univ_succ`.
- `gradedInclusion_eq_gradedSegmentSocle`: for a finite-length `π` with
  `T.IsSegmentSocle Δ π`, `gradedInclusion F T Δ.degree [π] = gradedSegmentSocle F T Δ`.
  It unfolds `gradedSegmentSocle` and rewrites with
  `segmentSocleClass_of_object`.
- `gradedInclusion_induced_eq_prod_of_length_eq_succ k`: for every datum with
  `d.length = k + 1` and segment-socle blocks,
  `gradedInclusion F T n [d.induced] = ∏ i, gradedSegmentSocle F T (d.segments i)`.

## Proofs

`gradedInclusion_induced_eq_prod_of_length_eq_succ`, by induction on `k`:

- `k = 0` (one segment, index `i`): `SegmentProductOrderedAssembly.singletonIso`
  identifies `d.induced` with the rank cast of `d.blocks i`, so the classes agree
  (`ofObject_eq_of_iso`). `gradedInclusion_rankCast` removes the rank cast,
  `gradedInclusion_eq_gradedSegmentSocle` gives `ζ(Δ_i)`, and the product over the
  one-element index type is that factor (`Fintype.prod_subsingleton`).
- `k + 1` (length `k + 2`): `SegmentProductSplit.nonempty_iso_binary` gives an
  isomorphism of `d.induced` with the rank cast of the binary normalized product
  of the head block `A` and the tail product `B = (tail d h).induced`. `A` has
  finite length (it is irreducible), and `B` has finite length by
  `hasFiniteLength_induced` (the tail datum has segment socles,
  `SegmentProductSplit.tail_hasSegmentSocles`); the binary product has finite
  length by `binaryProduct_preservesFiniteLength`. Then:
  1. `ofObject_eq_of_iso` and `gradedInclusion_rankCast` reduce the class of
     `d.induced` to the class of the binary product in rank
     `headRank + tailRank`;
  2. `binaryProductK0_classes` rewrites it as `binaryProductK0 F T hx [A] [B]`;
  3. `gradedMultiplication_homogeneous` turns this into the product
     `gradedInclusion [A] * gradedInclusion [B]` in the graded ring;
  4. the first factor is `ζ(head segment)` by `gradedInclusion_eq_gradedSegmentSocle`,
     and the second is `∏ j, ζ(tail segment j)` by the induction hypothesis
     applied to the tail datum (length `k + 1`);
  5. `prod_segments_eq_head_mul_tail` reassembles the product over `d`.

Main theorem: `map_prod` and `MvPolynomial.eval₂Hom_X'` rewrite the right side
as `∏ i, gradedSegmentSocle F T (d.segments i)`. If `d.length = 0`, then
`n = 0` (from `d.degree_sum`), the product is empty, hence equal to the ring unit
`gradedUnit F T`, and `zeroDatumUnitIso` identifies `d.induced` with
`T.binaryProductUnit`, whose graded class is `gradedUnit F T`. Otherwise
`d.length = k + 1` and the previous lemma applies.
