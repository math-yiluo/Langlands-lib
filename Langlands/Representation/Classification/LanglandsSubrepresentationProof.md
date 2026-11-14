# Langlands heads in reversed standard modules: proof

Module `Langlands.Representation.Classification.LanglandsSubrepresentationProof`,
namespace `Langlands.Classification`. The theorem
`langlandsSubrepresentationRealization` proves exactly the published proposition
`LanglandsSubrepresentationRealization`. It keeps the independent universes `uF` and `uV`
and adds no hypothesis. The auxiliary lemmas live in the namespace
`Langlands.Classification.LanglandsSubrepresentation`.

## Route

The proof uses smooth duality. It follows the route described in the statement's
Markdown. Let `d` be the datum, with segment-head blocks, in which no later segment
precedes an earlier one.

- `d.dual` is the existing same-order dual datum (`SegmentProductDatum.dual`): the segments
  are `(d.segments i).dual` and the blocks are the smooth contragredients of the blocks of
  `d`, in the same index order. `hh.dual` says that its blocks are again segment heads.
- `dual_isPrecedenceOrdered`: by `Segment.precedes_dual_iff`, the hypothesis that no later
  segment of `d` precedes an earlier one is exactly `d.dual.IsPrecedenceOrdered`.
- `d.contragredientInducedIso hh` is the existing isomorphism
  `d.induced.contragredient ≅ d.dual.induced`.
- `dual_multisegment` and `map_dual_map_dual`: the multisegment of `d.dual` is the
  segment-wise dual of the multisegment of `d`, and dualizing twice gives back the original
  multisegment (`Segment.dual_dual`).
- `dual_dual_segments_list`: the ordered segment list of `d.dual.dual` equals that of `d`.
  The Library's `nonempty_headProduct_iso_of_segmentList_eq` (from
  `OrderedSegmentHeadProductIndependence`) then gives an isomorphism
  `d.dual.dual.induced ≅ d.induced`, because both data have segment-head blocks.
- `isSubrepresentation_of_iso_right` and `isSubrepresentation_of_iso_left`: two generic
  lemmas that move `SmoothRep.IsSubrepresentation` along an isomorphism of the target or of
  the source. The proof composes the injective intertwiner with the isomorphism.

Admissibility of irreducible representations comes from the published cuspidal embedding
theorem `CuspidalSupport.cuspidalEmbedding`, whose first component gives
`SmoothRep.IsAdmissible`. Compact-open cofinality of `GL_n(F)` is
`GeneralLinear.compactOpen_cofinal`.

## Clause 2, positive rank (`isLanglandsHead_of_subrepresentation`)

Let `σ` be irreducible, and let `j : σ ⟶ d.induced` be injective.

1. `σ` is admissible, so `SmoothRep.isIrreducible_contragredient_iff` makes `σ.contragredient`
   irreducible.
2. By smooth exactness (`contragredientMap_surjective_of_injective_of_compact_cofinal`), the
   dual map `contragredientMap j : d.induced.contragredient → σ.contragredient` is
   surjective. The inverse of `contragredientInducedIso` is a surjection
   `d.dual.induced → d.induced.contragredient`.
3. `orderedMultisegmentHeadExistence`, applied to the precedence-ordered datum `d.dual`,
   gives a strong irreducible head `π₀` of `d.dual.induced`.
   `IsIrreducibleHead.nonempty_equiv_of_quotient_of_surjective` takes these two surjections
   separately and gives an equivalence between `σ.contragredient` and `π₀`.
   `IsIrreducibleHead.of_targetEquiv` then makes `σ.contragredient` the strong head of
   `d.dual.induced`. Hence `d.dual.IsLanglandsHead σ.contragredient`.
4. `SegmentProductDatum.IsLanglandsHead.contragredient`, which needs positive rank, turns
   this into `d.dual.dualReverse.IsLanglandsHead σ.contragredient.contragredient`.
   Admissible biduality (`SmoothRep.bidualIso`) and `of_targetEquiv` transfer the head to
   `σ`.
5. The multisegment of `d.dual.dualReverse` is `d.multisegment`: use
   `dualReverse_multisegment`, `dual_multisegment` and `map_dual_map_dual`. So
   `d.multisegment.IsLanglandsHead σ` holds, with witness datum `d.dual.dualReverse`.

## Clause 1, positive rank (`isSubrepresentation_of_isLanglandsHead`)

Let `π` satisfy `d.multisegment.IsLanglandsHead π`.

1. `orderedMultisegmentHeadExistence` for `d.dual` gives an irreducible `π₀` and a
   surjective intertwiner `q₀ : d.dual.induced → π₀`. Since `π₀` is admissible,
   `π₀.contragredient` is irreducible.
2. `contragredientMap_injective_of_surjective` makes `contragredientMap q₀` an injective
   intertwiner `π₀.contragredient → d.dual.induced.contragredient`. Transport it along
   `d.dual.contragredientInducedIso hh.dual : d.dual.induced.contragredient ≅ d.dual.dual.induced`,
   then along the isomorphism `d.dual.dual.induced ≅ d.induced` above. This embeds
   `π₀.contragredient` into `d.induced`.
3. Clause 2 then shows that `π₀.contragredient` is a Langlands head of `d.multisegment`.
4. `multisegmentHeadClassification` compares two Langlands heads of the same multisegment
   and gives an isomorphism `π ≅ π₀.contragredient`. Transporting the embedding along it
   gives `SmoothRep.IsSubrepresentation π d.induced`.

## Rank zero

- `rankZero_index_elim`: a rank-zero datum has no segments, because each segment has
  positive degree and the degrees sum to `0`. So every rank-zero datum is precedence-ordered,
  and `orderedMultisegmentHead_rankZero` makes `d.induced` a strong irreducible head of itself.
- Clause 1 (`isSubrepresentation_of_isLanglandsHead_rankZero`): `d.induced` is a Langlands head
  of `d.multisegment`, witnessed by `d` itself. `multisegmentHeadClassification` gives
  `π ≅ d.induced`, and this isomorphism is the embedding.
- Clause 2 (`isLanglandsHead_of_irreducible_rankZero`): `rankZeroNormalizedProductLinearEquiv`
  gives a linear equivalence between the carrier of the empty product and `ℂ`. Since `GL_0(F)` is
  trivial, `isIrreducibleQuotient_of_subsingleton_linearEquiv` gives a surjective
  intertwiner `d.induced → σ` for every irreducible `σ`.
  `IsIrreducibleHead.nonempty_equiv_of_quotient` and `of_targetEquiv` then make `σ` the head,
  witnessed by `d`. The subrepresentation hypothesis is not needed in rank zero.

The main theorem splits on `n = 0` or `0 < n` and puts the two clauses together.

## Provenance

This is an internal proof assembled from published Library results. It does not follow a
single printed proof. The duality route is the one recorded in the Markdown of
`LanglandsSubrepresentationStatement`, which cites Zelevinsky 1980, §§3.3, 9.1, 9.4, and
Jantzen 2007, §1.2. The proof imports the published proofs of ordered head existence
(`orderedMultisegmentHeadExistence`), multisegment head classification
(`multisegmentHeadClassification`), duality of Langlands heads
(`IsLanglandsHead.contragredient`), the cuspidal embedding theorem, and smooth-dual
exactness. It adds no axioms and introduces no new definitions.
