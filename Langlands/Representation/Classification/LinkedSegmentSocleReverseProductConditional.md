# Zelevinsky 1980 Proposition 4.6 from its inputs

Module `Langlands.Representation.Classification.LinkedSegmentSocleReverseProductConditional`,
namespace `Langlands.Classification`.

This module proves Zelevinsky, *Induced representations of reductive p-adic groups
II* (1980), Proposition 4.6, as stated in
`LinkedSegmentSocleReverseProductStructure F T`, from seven statements that it
takes as hypotheses. It follows the proof in the source (printed pp.185–186). The
source proof has three steps: (1) the juxtaposed case, (2) a nonzero map from
`π = ⟨Δ⟩ × ⟨Δ'⟩` to `ω`, the product for the union and the intersection, and
(3) an induction on the degree through the highest derivative. The derivative
part of step (3) is the abstract lemma
`FunctorLengthTwo.lengthTwo_of_strictMono` (module
`Filtration.FunctorLengthTwoDetection`). Nothing here is assumed beyond the
hypotheses listed below and published Library results.

## Helper lemmas

- `forall_ne_of_length_eq_two d h₂ P h01 h10`: for a datum `d` of length two, a
  property `P` of ordered pairs of segments holds for all pairs of distinct
  indices once it holds for `(0, 1)` and `(1, 0)`.
- `Segment.filterMap_eq_dropLastList l`: filtering `l` by the function of the highest
  derivative statement (f) (keep `⟨Δ.base, Δ.length - 1⟩` when `2 ≤ Δ.length`,
  drop `Δ` otherwise) gives the published `Segment.dropLastList l` of
  `Classification.SegmentInitialTruncation`. This shared lemma is reused from that module.
- `dropLastList_singleton J`: `Segment.dropLastList [J]` is `J.dropLast.toList`.
- `isIrreducible_of_isUnlinked hirr e hn hes hu`: a datum `e` of positive degree
  with segment socles and pairwise nonlinked segments has an irreducible induced
  representation. This is `UnlinkedSegmentSocleProductIrreducible F T` (Ze80
  Theorem 4.2, (2)⇒(1)) after writing the degree as `m + 1`.

## The theorem

`linkedSegmentSocleReverseProductStructure_of hψ hex hirr hA hB he hf :
LinkedSegmentSocleReverseProductStructure.{uF, uV} F T`. The hypotheses are:

- `hψ : HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement F T`:
  `F` has a nontrivial unitary additive character `ψ`.
- `hex : SegmentZelevinskyConstituentExistence F T` (Ze80 §3.1): every segment
  has a segment socle.
- `hirr : UnlinkedSegmentSocleProductIrreducible F T` (Ze80 Theorem 4.2,
  (2)⇒(1)): a product of segment socles with pairwise nonlinked segments is
  irreducible.
- `hA : JuxtaposedSegmentSocleReverseProductStructure F T`: step (1), the
  conclusion of Proposition 4.6 when `Δ'` is juxtaposed with `Δ`.
- `hB : LinkedSegmentSocleReverseProductQuotientHom F T`: step (2), a nonzero
  intertwining map from `⟨Δ⟩ × ⟨Δ'⟩` to every product of socles of the union
  followed by the optional intersection.
- `he : NonjuxtaposedSegmentSocleDerivativeStrictMono F T`: for a product of
  segment socles with pairwise nonjuxtaposed segments, `K ↦` the image of the
  derivative of order `λ = ∑ rank` of the inclusion of `K` is strictly
  monotone on subrepresentations (the lattice form of Ze80 4.3).
- `hf : SegmentSocleProductHighestDerivative F T`: the derivative of order `λ`
  of a product of segment socles is isomorphic to a product of the socles of the
  end-truncated segments (singletons dropped).

The published `cuspidalIntegralTwistFreeness F T` supplies the twist-freeness
hypothesis of the segment combinatorics.

Proof. Fix `ψ` from `hψ`. The proof is by strong induction on the degree `n`.
Let `d` be a datum of length two with segment socles, `Δ = d.segments 0`,
`Δ' = d.segments 1`, and `Δ'` preceding `Δ`.

1. If `Δ'` is juxtaposed with `Δ`, `hA` gives the conclusion.
2. Otherwise `Segment.Precedes.truncation` (module
   `Classification.SegmentPrecedenceTruncation`) gives: both segments have
   length at least two; the union `U` (length at least two) and the
   intersection `J` replace `Δ, Δ'`; `Δ'⁻` precedes `Δ⁻`; the union and
   intersection of `Δ⁻, Δ'⁻` are `U⁻` and `J⁻` (where `J⁻` is absent if `J` is a
   singleton); all four segments have the same rank; and `J ⊆ U`. Here `Δ⁻` is
   the published `Segment.dropLastNonempty` and `J⁻` the optional
   `Segment.dropLast` of `Classification.SegmentInitialTruncation`.
3. Let `e = ofSegmentList [U, J]` (module
   `Classification.SegmentSocleProductComparison`), of degree `n` by the degree
   identity of the replacement. It has segment socles by `hex`. Since `J ⊆ U`,
   `U` and `J` are not linked, so `ω = e.induced` is irreducible by `hirr`.
4. `hB` gives a nonzero intertwining map `f : π → ω`.
5. Let `λ` be the sum of the ranks of `Δ` and `Δ'`, which equals the sum of the
   ranks of `U` and `J`. Since `Δ` and `Δ'` are not juxtaposed in either order,
   `he` makes the images of the order-`λ` derivative strictly monotone on
   subrepresentations of `π`. By `hf`, the order-`λ` derivative of `π` is
   isomorphic to `d'.induced` for a datum `d'` with segments `Δ⁻, Δ'⁻` and
   segment socles.
6. The induction hypothesis applied to `d'` (degree `n - λ < n`) gives a union
   and intersection replacement and a product `e'` with the conclusion of the
   proposition for `d'.induced`. By `IsUnionIntersectionReplacement.unique`,
   the replacement is `U⁻, J⁻`. By `hf`, the order-`λ` derivative of `ω` is a
   product of socles with segments `U⁻ :: J⁻.toList`, and by
   `nonempty_iso_of_ofFn_segments_eq` it is isomorphic to `e'.induced`.
   So the derivative of `ω` is irreducible.
7. `FunctorLengthTwo.exists_middle_of_equiv` transports the lattice description
   of `d'.induced` to the derivative of `π`: its subrepresentations are `⊥`, a
   middle term `S` not equivalent to the derivative of `ω`, and `⊤`.
   `FunctorLengthTwo.lengthTwo_of_strictMono` applied to `f` then gives the
   two-step filtration of `π` with simple factors, top factor equivalent to `ω`,
   bottom factor not equivalent to `ω`, and bottom step the unique irreducible
   subrepresentation. Together with `U`, `some J` and `e` this is the
   conclusion.
