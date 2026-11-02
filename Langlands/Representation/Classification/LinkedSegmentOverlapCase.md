# The overlapping case of Proposition 4.6, step (2)

Author: Worker 1033.

Step (2) of Zelevinsky 1980, Proposition 4.6 (printed p. 186) treats linked,
non-juxtaposed segments, where `Δ'` precedes `Δ`. Write `Δ' = init ∪ term` with
`term = Δ ∩ Δ'`. Then `init` precedes `Δ` and is juxtaposed with it, and
`Δ ∪ init = Δ ∪ Δ'`. Zelevinsky's argument has three steps:

- Frobenius reciprocity reduces the claim to a nonzero map from the Jacquet
  module `σ`;
- the geometric lemma (Corollary 1.3) together with 3.4 and 1.5 give the
  quotient `(⟨Δ⟩ × ⟨init⟩) ⊗ ⟨term⟩` of `σ`;
- step (1) for the juxtaposed pair `Δ`, `init` maps `⟨Δ⟩ × ⟨init⟩` onto
  `⟨Δ ∪ Δ'⟩`.

This module implements that argument. It takes three hypotheses:

- `h1 : JuxtaposedSegmentSocleReverseProductStructure F T`, step (1);
- `h34 : SegmentSocleJacquetFormula F T`, Ze80 3.4;
- `h13 : Geometric.PadicIdentityCellQuotientTheorem.{uF, max uF uV}`, Ze80
  Corollary 1.3 in natural form, with the Library statement module
  `Geometric/IdentityCellQuotientStatement`.

Zelevinsky's appeal to 1.5 (Jacquet modules of products) is replaced by the
explicit computation of the identity geometric piece in
[LinkedSegmentOverlapPiece](LinkedSegmentOverlapPiece.md). Everything lives in
the namespace `Langlands.Classification.QuotientHom`.

## Generic lemmas

- `isIrreducible_of_isSegmentSocle`: a segment socle is irreducible. This is
  the first component of the `IsIrreducibleSocle` clause of the published
  `IsSegmentSocle`.
- `nonempty_socleEquiv`: two segment socles of one segment are equivalent.
  Both are isomorphic to the published segment socle by
  `IsSegmentSocle.nonempty_iso_segmentSocle`.
- `comp_ne_zero_of_surjective`: a nonzero intertwiner precomposed with a
  surjective one is nonzero.
- `exists_surjective_of_juxtaposed h1 d …`: step (1) as a surjection. Let `d`
  be a two-segment socle datum with juxtaposed `d.segments 1 ≺ d.segments 0`
  and replacement `(U, none)`, and let `e` be any socle datum with segment
  list `[U]`. Then there is a surjective intertwiner `d.induced → e.induced`.
  The proof is that of `exists_ne_zero_of_juxtaposed` in
  [LinkedSegmentJuxtaposedCase](LinkedSegmentJuxtaposedCase.md): the
  projection onto graded piece `1` of the filtration from `h1`, followed by
  equivalences. As there, `replacement_eq_of_inter_empty` identifies the
  replacement from `h1` with `(U, none)`.
- `singleDatum U E₀`: the one-segment datum with block `E₀`.
  `singleDatum_segments` says its segment list is `[U]`.
  `nonempty_singleDatumEquiv` says its product is equivalent to `E₀`, by the
  published `singleBlockNormalizedProductEquiv` and
  `reindex_finCongr_symm_self`.
- `nonempty_parabolicInducedEquivOfEq`: normalized parabolic induction along a
  shape equal to `B`, of a factor heterogeneously equal to the external tensor
  of `τ`, is the normalized product induction of `τ`. The proof substitutes
  both equalities, and the result is `Representation.Equiv.refl`.

## The configuration-level theorem

For `O : OverlapConfig T n` (see
[LinkedSegmentOverlapShapes](LinkedSegmentOverlapShapes.md)):

- `nonempty_splitEquiv`: the isomorphism `ι` supplied by Ze80 3.4 for the split
  of `Δ'` becomes the hypothesis `E₁` of `LinkedSegmentOverlapPiece`. It is
  `SmoothRep.equivOfIso ι` followed by `externalTwoEquiv`.
- `nonempty_unionBlockEquiv`: the induced union block of
  `targetFactors A₀ π₁ π₂` is the normalized product induction of
  `unionBlocks A₀ π₁` along `unionShape`. This is
  `nonempty_parabolicInducedEquivOfEq` with `rfl` and `HEq.rfl`.
- `exists_unionProductSurjection`: assume `init ≺ Δ`, `init` is juxtaposed with
  `Δ`, the replacement of `(Δ, init)` is `(U, none)`, and `A₀`, `π₁`, `E₀` are
  socles of `Δ`, `init`, `U`. Then step (1) for the datum
  `⟨2, ![Δ, init], hU, unionBlocks A₀ π₁⟩` gives a surjection onto
  `(singleDatum U E₀).induced`.
- `exists_unionSurjection`: the same surjection, with source the induced union
  block and target `E₀`. It is composed with the two equivalences above.
- `n_pos`: `0 < n`, since `deg Δ > 0`.
- `exists_ne_zero O h1 h34 h13 hpre hjux hrep A hA₀ hA₁ E hE₀ hE₁`: let `A 0`,
  `A 1` be socles of `Δ`, `Δ'`, and `E 0`, `E 1` socles of `U`, `term`. Then
  there is a nonzero intertwiner from the product of `A` along `B` to the
  product of `E` along `C`. The proof:
  - Ze80 3.4 for `(Δ', A 1)` at the split `q` gives socles `π₁` of `init` and
    `π₂` of `term`, and `E₁` by `nonempty_splitEquiv`;
  - `h13`, at `O.n_pos`, `O.B`, `O.C`, `O.S`, `O.R`, `O.hS`, `O.hR`, gives the
    natural surjection `η` onto the identity geometric piece;
  - `exists_unionSurjection` gives `f₀`;
  - `nonempty_socleEquiv` gives `f₁ : π₂ ≃ E 1`;
  - `exists_ne_zero_of_identityPiece` of
    [LinkedSegmentOverlapAssembly](LinkedSegmentOverlapAssembly.md) concludes,
    using the irreducibility of `E 0` and `E 1`.

## The datum-level theorem

`exists_ne_zero_of_overlap h1 h34 h13 d h₂ hd U J e q hq hqm hJ hpre hjux hrep
hdeg he he'` takes:

- a two-segment socle datum `d`, with `Δ = d.segments 0` and
  `Δ' = d.segments 1`;
- a split point `q` with `Δ'.terminal q hqm = J`, where `init = Δ'.initial q hq`
  precedes `Δ`, is juxtaposed with it, and has replacement `(U, none)`;
- the degree identity `hdeg : deg U = deg Δ + deg init`;
- a socle datum `e` with segment list `[U, J]`.

It produces a nonzero intertwiner `d.induced → e.induced`. The proof first
destructures `d` and `e`. Then it substitutes `d.length = 2`, `e.length = 2`,
`e.segments = ![U, J]` and `J = term`, and builds the `OverlapConfig`. The
blocks of `d` are repackaged with `Fin.cons` as the blocks `A` of the shape
`O.B`. The resulting datum `d₂` has the same segments, so
`nonempty_induced_iso_of_segments_eq` gives `d.induced ≅ d₂.induced`. The
blocks of `e` are used directly, since after substitution its shape is `O.C`.
`exists_ne_zero` then gives the map from `d₂.induced`. Precomposing with the
isomorphism keeps it nonzero (`comp_ne_zero_of_surjective`).

Several declarations have a raised heartbeat limit.
