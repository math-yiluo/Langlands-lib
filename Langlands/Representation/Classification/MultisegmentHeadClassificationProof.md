# Multisegment-head classification

Author: Worker 4879. The reduction lemma reuses the shared task draft by
Worker 1733 (previous instance).

`Langlands.Classification.multisegmentHeadClassification.{uF, uV}` proves
exactly the published proposition
`Langlands.Classification.MultisegmentHeadClassification.{uF, uV} F T` of
`Langlands/Representation/Classification/MultisegmentClassificationStatement.lean`.
Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`,
with `uF` and `uV` independent. It adds no premise. The statement asserts, for
every rank `n` (including `0`), all multisegments `a b` and all smooth
representations `π π'` of `GL_n(F)` with `a.IsLanglandsHead π` and
`b.IsLanglandsHead π'`, that `a = b ↔ Nonempty (π ≅ π')`. Both directions are
proved.

## Implemented proof

The module has two theorems.

### `multisegmentHeadClassification_of_ordered`

This lemma derives `MultisegmentHeadClassification.{uF, uV} F T` from the
ordered classification `OrderedMultisegmentHeadClassification.{uF, uV} F T`,
which it takes as an explicit premise. Fix `n`, `a`, `b`, `π`, `π'` and the two
head hypotheses. By the definition `Multisegment.IsLanglandsHead`
(`LanglandsData.lean`), the hypotheses supply segment product data
`d d' : T.SegmentProductDatum n` with `d.multisegment = a`,
`d'.multisegment = b`, `d.IsLanglandsHead π` and `d'.IsLanglandsHead π'`.
The published lemma
`PadicField.TopologicalData.SegmentProductDatum.IsLanglandsHead.isLanglandsQuotient`
drops the kernel-uniqueness clause of each head and keeps the precedence
ordering, the segment-head blocks and the irreducible quotient map. The
ordered classification applied to `d`, `d'`, `π`, `π'` and these two quotient
relations gives `d.multisegment = d'.multisegment ↔ Nonempty (π ≅ π')`.
Rewriting with the two multisegment equalities gives the target equivalence.
The argument does not depend on the rank, so rank `0` needs no separate case.

### `multisegmentHeadClassification`

The main theorem applies the lemma to an unconditional proof of the ordered
classification, built from three published Library results:

- `orderedMultisegmentHeadClassification_of_squareIntegrable`
  (`OrderedMultisegmentHeadClassificationReduction.lean`) proves
  `SquareIntegrableLanglandsClassification F T →
  SegmentSpecialParameterUniqueness F T →
  OrderedMultisegmentHeadClassification F T`. It treats rank `0` directly.
  In positive rank it converts each segment datum into square-integrable
  Langlands data through `orderedSegmentSquareIntegrableConversion` and
  translates block matching into equality of segment multisets.
- `squareIntegrableLanglandsClassification`
  (`SquareIntegrableLanglandsClassificationProof.lean`) proves the first
  premise.
- `segmentSpecialParameterUniqueness`
  (`SegmentSpecialParameterUniquenessProof.lean`) proves the second premise.

All three are used at the universe pair `{uF, uV}` and at the given `F` and
`T`. The proof defines no new theorem for the ordered target, which is the
deliverable of task `879da351-11ad-49aa-9162-4dbd3d01829c`; it only applies
the published reduction to the two published premise proofs. All segment
carriers, blocks and output representations stay at universe `max uF uV`. The
axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The target is F. Rodier, *Représentations de GL(n,k) où k est un corps
p-adique*, Séminaire Bourbaki, exposé 587, Astérisque 92–93 (1982), §4.3,
Theorem 3(b), printed pp.211–212 (PDF pp.12–13), registered as
`rodier-1982-gln`. Rodier compares segment lists up to order; the published
statement expresses this as equality of multisets. The Lean route above
follows the Library's reduction to the square-integrable Langlands
classification and the injectivity of the segment parameter of special heads,
rather than Rodier's written argument.
